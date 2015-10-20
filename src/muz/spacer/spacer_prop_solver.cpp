/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    prop_solver.cpp

Abstract:

    SMT solver abstraction for SPACER.

Author:

    Krystof Hoder (t-khoder) 2011-8-17.

Revision History:

    Modified by Anvesh Komuravelli

--*/

#include <sstream>
#include "model.h"
#include "spacer_util.h"
#include "spacer_prop_solver.h"
#include "ast_smt2_pp.h"
#include "dl_util.h"
#include "model_pp.h"
#include "smt_params.h"
#include "datatype_decl_plugin.h"
#include "bv_decl_plugin.h"
#include "spacer_farkas_learner.h"
#include "ast_smt2_pp.h"
#include "expr_replacer.h"
#include "fixedpoint_params.hpp"

//
// Auxiliary structure to introduce propositional names for assumptions that are not
// propositional. It is to work with the smt::context's restriction
// that assumptions be propositional literals.
//

namespace spacer {

    class prop_solver::safe_assumptions {
        prop_solver&        s;
        ast_manager&        m;
        expr_ref_vector     m_hard_atoms;
        expr_ref_vector     m_soft_atoms;
        expr_ref_vector     m_assumptions;
        obj_map<app,expr *> m_proxies2expr;
        obj_map<expr, app*> m_expr2proxies;
        unsigned            m_num_proxies;

        app * mk_proxy(expr* literal) {
            app* res;
            SASSERT(!is_var(literal)); //it doesn't make sense to introduce names to variables
            if (m_expr2proxies.find(literal, res)) {
                return res;
            }
            SASSERT(s.m_proxies.size() >= m_num_proxies);
            if (m_num_proxies == s.m_proxies.size()) {
                std::stringstream name;
                name << "spacer_proxy_" << s.m_proxies.size();
                res = m.mk_const(symbol(name.str().c_str()), m.mk_bool_sort());
                s.m_proxies.push_back(res);
            }
            else {
                res = s.m_proxies[m_num_proxies].get();
            }
            ++m_num_proxies;
            m_expr2proxies.insert(literal, res);
            m_proxies2expr.insert(res, literal);
            expr_ref implies(m.mk_or(m.mk_not(res), literal), m);
            s.m_ctx->assert_expr(implies);
            m_assumptions.push_back(implies);
            TRACE("spacer_verbose", tout << "name asserted " << mk_pp(implies, m) << "\n";);    
            return res;
        }

        void mk_safe(expr_ref_vector& conjs) {
            qe::flatten_and(conjs);
            expand_literals(conjs);
            for (unsigned i = 0; i < conjs.size(); ++i) {
                expr * lit = conjs[i].get();
                expr * lit_core = lit;
                m.is_not(lit, lit_core);
                SASSERT(!m.is_true(lit));
                if (!is_uninterp(lit_core) || to_app(lit_core)->get_num_args() != 0) {
                    conjs[i] = mk_proxy(lit);
                }
            }
            m_assumptions.append(conjs);
        }

        expr* apply_accessor(
            ptr_vector<func_decl> const& acc,
            unsigned j,
            func_decl* f,
            expr* c) {
            if (is_app(c) && to_app(c)->get_decl() == f) {
                return to_app(c)->get_arg(j);
            }
            else {
                return m.mk_app(acc[j], c);
            }
        }

        void expand_literals(expr_ref_vector& conjs) {
            arith_util arith(m);
            datatype_util dt(m);
            bv_util       bv(m);
            expr* e1, *e2, *c, *val;
            rational r;
            unsigned bv_size;

            TRACE("expand_literals", 
                  tout << "begin expand\n";
                  for (unsigned i = 0; i < conjs.size(); ++i) {
                      tout << mk_pp(conjs[i].get(), m) << "\n";
                  });

            for (unsigned i = 0; i < conjs.size(); ++i) {
                expr* e = conjs[i].get();
                if (m.is_eq(e, e1, e2) && arith.is_int_real(e1)) {
                    conjs[i] = arith.mk_le(e1,e2);
                    if (i+1 == conjs.size()) {
                        conjs.push_back(arith.mk_ge(e1, e2));
                    }
                    else {
                        conjs.push_back(conjs[i+1].get());
                        conjs[i+1] = arith.mk_ge(e1, e2);
                    }
                    ++i;
                }
                else if ((m.is_eq(e, c, val) && is_app(val) && dt.is_constructor(to_app(val))) ||
                         (m.is_eq(e, val, c) && is_app(val) && dt.is_constructor(to_app(val)))){
                    func_decl* f = to_app(val)->get_decl();
                    func_decl* r = dt.get_constructor_recognizer(f);
                    conjs[i] = m.mk_app(r, c);
                    ptr_vector<func_decl> const& acc = *dt.get_constructor_accessors(f);
                    for (unsigned j = 0; j < acc.size(); ++j) {
                        conjs.push_back(m.mk_eq(apply_accessor(acc, j, f, c), to_app(val)->get_arg(j)));
                    }
                }
                else if ((m.is_eq(e, c, val) && bv.is_numeral(val, r, bv_size)) ||
                         (m.is_eq(e, val, c) && bv.is_numeral(val, r, bv_size))) {
                    rational two(2);
                    for (unsigned j = 0; j < bv_size; ++j) {
                        parameter p(j);
                        //expr* e = m.mk_app(bv.get_family_id(), OP_BIT2BOOL, 1, &p, 1, &c);
                        expr* e = m.mk_eq(m.mk_app(bv.get_family_id(), OP_BIT1), bv.mk_extract(j, j, c));
                        if ((r % two).is_zero()) {
                            e = m.mk_not(e);
                        }
                        r = div(r, two);
                        if (j == 0) {
                            conjs[i] = e;
                        }
                        else {
                            conjs.push_back(e);
                        }
                    }
                }
            }
            TRACE("expand_literals", 
                  tout << "end expand\n";
                  for (unsigned i = 0; i < conjs.size(); ++i) {
                      tout << mk_pp(conjs[i].get(), m) << "\n";
                  });
        }

    public:
        safe_assumptions(prop_solver& s,
                         expr_ref_vector const& hard_assumptions,
                         expr_ref_vector& soft_assumptions):
            s(s), m(s.m), m_hard_atoms(hard_assumptions), m_soft_atoms (soft_assumptions),
            m_assumptions(m), m_num_proxies(0) {
              mk_safe(m_hard_atoms);
              mk_safe(m_soft_atoms);
        }
        
        ~safe_assumptions() {
        }    
        
        expr_ref_vector const& hard_atoms() const { return m_hard_atoms; }

        expr_ref_vector& soft_atoms() { return m_soft_atoms; }
        
        unsigned assumptions_size() const { return m_assumptions.size(); }
        
        expr* assumptions(unsigned i) const { return m_assumptions[i]; }

        void undo_proxies(expr_ref_vector& es) {
            expr_ref e(m);
            expr* r;
            for (unsigned i = 0; i < es.size(); ++i) {
                e = es[i].get();
                if (is_app(e) && m_proxies2expr.find(to_app(e), r)) {
                    es[i] = r;
                }
            }
        }
        
        void elim_proxies(expr_ref_vector& es) {
            expr_substitution sub(m, false, m.proofs_enabled());
            proof_ref pr(m);
            if (m.proofs_enabled()) {
                pr = m.mk_asserted(m.mk_true());
            }
            obj_map<app,expr*>::iterator it = m_proxies2expr.begin(), end = m_proxies2expr.end();
            for (; it != end; ++it) {
                sub.insert(it->m_key, m.mk_true(), pr);
            }
            //scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
            scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer (m);
            rep->set_substitution(&sub);
            replace_proxies(*rep, es);
        }
    private:

        void replace_proxies(expr_replacer& rep, expr_ref_vector& es) {
            expr_ref e(m);
            for (unsigned i = 0; i < es.size(); ++i) {
                e = es[i].get();
                rep(e);
                es[i] = e;
                if (m.is_true(e)) {
                    es[i] = es.back();
                    es.pop_back();
                    --i;
                }
            }        
        }
    };


    prop_solver::prop_solver(manager& pm, fixedpoint_params const& p, symbol const& name, bool validate_theory_core) :
        m_fparams(pm.get_fparams()),
        m(pm.get_manager()),
        m_pm(pm),
        m_name(name),
        m_try_minimize_core(p.pdr_try_minimize_core()),
        m_ctx(pm.mk_fresh()),
        m_pos_level_atoms(m),
        m_neg_level_atoms(m),
        m_proxies(m),
        m_core(0),
        m_subset_based_core(false),
        m_uses_level(infty_level ()),
        m_delta_level(false),
        m_in_level(false),
        m_validate_theory_core (validate_theory_core)
    {
        m_ctx->assert_expr(m_pm.get_background());
    }

    void prop_solver::add_level() {
        unsigned idx = level_cnt();
        std::stringstream name;
        name << m_name << "#level_" << idx;
        func_decl * lev_pred = m.mk_fresh_func_decl(name.str().c_str(), 0, 0,m.mk_bool_sort());
        m_level_preds.push_back(lev_pred);

        app_ref pos_la(m.mk_const(lev_pred), m);
        app_ref neg_la(m.mk_not(pos_la.get()), m);

        m_pos_level_atoms.push_back(pos_la);
        m_neg_level_atoms.push_back(neg_la);

        m_level_atoms_set.insert(pos_la.get());
        m_level_atoms_set.insert(neg_la.get());
    }

    void prop_solver::ensure_level(unsigned lvl) {
        while (lvl>=level_cnt()) {
            add_level();
        }
    }

    unsigned prop_solver::level_cnt() const {
        return m_level_preds.size();
    }

    void prop_solver::push_level_atoms(unsigned level, expr_ref_vector& tgt) const {
        unsigned lev_cnt = level_cnt();
        for (unsigned i=0; i<lev_cnt; i++) {
            bool active = m_delta_level ? i == level : i>=level;
            app * lev_atom = active ? m_neg_level_atoms[i] : m_pos_level_atoms[i];
            tgt.push_back(lev_atom);
        }
    }

    void prop_solver::add_formula(expr * form) {
        SASSERT(!m_in_level);
        m_ctx->assert_expr(form);
        IF_VERBOSE(21, verbose_stream() << "$ asserted " << mk_pp(form, m) << "\n";);
        TRACE("spacer", tout << "add_formula: " << mk_pp(form, m) << "\n";);
    }

    void prop_solver::add_level_formula(expr * form, unsigned level) {
        ensure_level(level);
        app * lev_atom = m_pos_level_atoms[level].get();
        app_ref lform(m.mk_or(form, lev_atom), m);
        add_formula(lform.get());
    }


    lbool prop_solver::check_safe_assumptions(
        safe_assumptions& safe,
        const expr_ref_vector& hard_atoms,
        expr_ref_vector& soft_atoms)
    {
        flet<bool> _model(m_fparams.m_model, m_model != 0);
        expr_ref_vector expr_atoms(m);

        expr_atoms.append (hard_atoms);
        if (m_in_level) {
            push_level_atoms(m_current_level, expr_atoms);
        }
        unsigned num_non_soft = expr_atoms.size ();
        expr_atoms.append (soft_atoms);

        lbool result = m_ctx->check(expr_atoms);

        TRACE("spacer", 
               tout << mk_pp(m_pm.mk_and(expr_atoms), m) << "\n";
               tout << "num non soft atoms: " << num_non_soft << "\n";
               tout << result << "\n";
             );

        if (result == l_true && m_model) {
            m_ctx->get_model(*m_model);
            TRACE("spacer_verbose", model_pp(tout, **m_model); );
        }

        if (result == l_false && !soft_atoms.empty ()) {
            TRACE ("spacer", tout << "unsat using soft atoms\n";);
            TRACE ("spacer",
                    tout << "Core:\n";
                    for (unsigned i = 0; i < m_ctx->get_unsat_core_size(); ++i) {
                        tout << mk_pp (m_ctx->get_unsat_core_expr (i), m) << "\n";
                    }
                  );

            expr_ref atom_bkp (m);
            ast_eq_proc eq_proc;

            TRACE ("spacer",
                    tout << "soft atoms in core:\n";
                    for (unsigned i = num_non_soft; i < expr_atoms.size (); i++) {
                        bool found = false;
                        for (unsigned j = 0; j < m_ctx->get_unsat_core_size(); j++) {
                            if (eq_proc (expr_atoms.get (i), m_ctx->get_unsat_core_expr (j))) {
                                found = true;
                                break;
                            }
                        }
                        if (found) {
                            tout << mk_pp (expr_atoms.get (i), m) << "\n";
                        }
                    }
                  );

            // try to get a model with as many soft_atoms as possible,
            while (expr_atoms.size () > num_non_soft) {
                // remove the first atom in core
                unsigned core_size = m_ctx->get_unsat_core_size();
                unsigned num_atoms = expr_atoms.size ();
                bool found = false;
                for (unsigned i = num_non_soft; i < num_atoms; i++) {
                    for (unsigned j = 0; j < core_size; j++) {
                        if (eq_proc (expr_atoms.get (i), m_ctx->get_unsat_core_expr (j))) {
                            found = true;
                            break;
                        }
                    }
                    if (found) {
                        atom_bkp = expr_atoms.get (i);
                        expr_atoms[i] = expr_atoms.back ();
                        expr_atoms.pop_back ();
                        TRACE ("spacer",
                                tout << "removing soft atom: " << mk_pp (atom_bkp,m) << "\n";
                              );
                        break;
                    }
                }
                if (!found) {
                    // no soft atom in core
                    // drop all soft atoms
                    expr_atoms.resize (num_non_soft);
                    break;
                }

                // check sat with remaining assumptions
                result = m_ctx->check(expr_atoms);

                if (result == l_true) {
                    if (m_model) {
                        m_ctx->get_model(*m_model);
                        TRACE("spacer_verbose", model_pp(tout, **m_model); );
                    }
                    break;
                }

                if (result == l_undef) {
                    expr_atoms.push_back (atom_bkp);
                    break;
                }

                SASSERT (result == l_false);
            }

            // update soft_atoms
            soft_atoms.reset ();
            for (unsigned i = num_non_soft; i < expr_atoms.size (); i++) {
                soft_atoms.push_back (expr_atoms.get (i));
            }
            TRACE ("spacer", tout << "result: " << result << "\n";);
            TRACE ("spacer", tout << "subset of soft atoms\n";);
            TRACE ("spacer",
                    for (unsigned j = 0; j < soft_atoms.size (); ++j) {
                        tout << mk_pp (soft_atoms.get (j), m) << "\n";
                    }
                  );
        }

        SASSERT (result != l_false || soft_atoms.empty ());

        if (result == l_false) { 
            unsigned core_size = m_ctx->get_unsat_core_size(); 
            m_uses_level = infty_level ();
            
            for (unsigned i = 0; i < core_size; ++i) {
              expr* core = m_ctx->get_unsat_core_expr (i);
              if (m_level_atoms_set.contains (core))
              {
                unsigned sz = std::min (m_uses_level, m_neg_level_atoms.size ());
                for (unsigned j = 0; j < sz; ++j)
                  if (m_neg_level_atoms [j].get () == core)
                  {
                    m_uses_level = j;
                    break;
                  }
                SASSERT (!is_infty_level (m_uses_level));
              }
            }
        }

        if (result == l_false && m_core && m.proofs_enabled() && !m_subset_based_core) {
            TRACE ("spacer", tout << "theory core\n";);
            extract_theory_core(safe);
            // save the unsat core
            unsigned core_size = m_ctx->get_unsat_core_size ();
            expr_ref_vector unsat_core (m);
            for (unsigned i = 0; i < core_size; ++i) {
                unsat_core.push_back (m_ctx->get_unsat_core_expr (i));
            }
            if (m_validate_theory_core && !validate_theory_core ()) {
                TRACE ("spacer", tout << "theory core unsound; using subset core\n";);
                extract_subset_core (safe, unsat_core.c_ptr (), core_size);
            }
        }
        else if (result == l_false && m_core) {
            TRACE ("spacer", tout << "subset core\n";);
            extract_subset_core(safe);    
            SASSERT(expr_atoms.size() >= m_core->size());
        }
        m_core = 0;
        m_model = 0;
        m_subset_based_core = false;
        return result;
    }

    bool prop_solver::validate_theory_core () {
        expr_ref_vector atoms (m);
        if (!m_core->empty ()) {
            expr_ref_vector _aux (m);
            safe_assumptions safe (*this, *m_core, _aux);
            atoms.append (safe.hard_atoms ());
        }
        if (m_in_level) {
            push_level_atoms (m_current_level, atoms);
        }

        TRACE ("spacer",
                tout << "Check theory core\n";
                tout << mk_pp(m_pm.mk_and(atoms), m) << "\n";
              );

        lbool result = m_ctx->check (atoms);

        TRACE ("spacer",
                tout << result << "\n";
              );

        return (result == l_false);
    }

    void prop_solver::extract_subset_core(safe_assumptions& safe, expr* const* unsat_core, unsigned unsat_core_size) {
        unsigned core_size = unsat_core ? unsat_core_size : m_ctx->get_unsat_core_size(); 
        m_core->reset();
        for (unsigned i = 0; i < core_size; ++i) {
            expr * core_expr = unsat_core ? unsat_core[i] : m_ctx->get_unsat_core_expr(i);
            SASSERT(is_app(core_expr));

            if (m_level_atoms_set.contains(core_expr)) {
                continue;
            }
            if (is_aux_predicate(core_expr)) {
                continue;
            }
            m_core->push_back(to_app(core_expr));
        }        

        safe.undo_proxies(*m_core);

        TRACE("spacer", 
            tout << "core_exprs: ";
                for (unsigned i = 0; i < core_size; ++i) {
                tout << mk_pp(unsat_core ? unsat_core[i] : m_ctx->get_unsat_core_expr(i), m) << " ";
            }
            tout << "\n";
            tout << "core: " << mk_pp(m_pm.mk_and(*m_core), m) << "\n";              
        );
    }


    void prop_solver::extract_theory_core(safe_assumptions& safe) {
        proof_ref pr(m);
        pr = m_ctx->get_proof();
        IF_VERBOSE(21, verbose_stream() << mk_ismt2_pp(pr, m) << "\n";);
        farkas_learner fl(m_fparams, m);
        expr_ref_vector lemmas(m);
        obj_hashtable<expr> bs;
        for (unsigned i = 0; i < safe.assumptions_size(); ++i) {
            bs.insert(safe.assumptions(i));
        }
        fl.get_lemmas(pr, bs, lemmas);
        safe.elim_proxies(lemmas);
        fl.simplify_lemmas(lemmas); // redundant?

        bool outside_of_logic =
            (m_fparams.m_arith_mode == AS_DIFF_LOGIC &&
             !is_difference_logic(m, lemmas.size(), lemmas.c_ptr())) ||
            (m_fparams.m_arith_mode == AS_UTVPI &&
             !is_utvpi_logic(m, lemmas.size(), lemmas.c_ptr()));

        if (outside_of_logic) {
            IF_VERBOSE(2, 
                       verbose_stream() << "not diff\n";
                       for (unsigned i = 0; i < lemmas.size(); ++i) {
                           verbose_stream() << mk_pp(lemmas[i].get(), m) << "\n";
                       });
            TRACE ("spacer", 
                       tout << "not diff\n";
                       for (unsigned i = 0; i < lemmas.size(); ++i) {
                           tout << mk_pp(lemmas[i].get(), m) << "\n";
                       });
            extract_subset_core(safe);
        }        
        else {

            IF_VERBOSE(2, 
                       verbose_stream() << "Lemmas\n";            
                       for (unsigned i = 0; i < lemmas.size(); ++i) {
                           verbose_stream() << mk_pp(lemmas[i].get(), m) << "\n";
                       });
            TRACE ("spacer", 
                       tout << "Lemmas\n";            
                       for (unsigned i = 0; i < lemmas.size(); ++i) {
                           tout << mk_pp(lemmas[i].get(), m) << "\n";
                       });

            m_core->reset();
            m_core->append(lemmas);
        }
    }

    lbool prop_solver::check_assumptions (const expr_ref_vector & hard_atoms,
                                          expr_ref_vector& soft_atoms,
                                          unsigned num_bg, expr * const * bg) 
    {
        spacer::smt_context::scoped _scoped(*m_ctx);
        safe_assumptions safe(*this, hard_atoms, soft_atoms);
        for (unsigned i = 0; i < num_bg; ++i) m_ctx->assert_expr (bg [i]);
        
        lbool res = check_safe_assumptions(safe, safe.hard_atoms(), safe.soft_atoms());

        //
        // we don't have to undo model naming, as from the model 
        // we extract the values for state variables directly
        //
        soft_atoms.reset ();
        soft_atoms.append (safe.soft_atoms ());
        return res;
    }

    void prop_solver::collect_statistics(statistics& st) const {
    }

    void prop_solver::reset_statistics() {
    }

    


}
