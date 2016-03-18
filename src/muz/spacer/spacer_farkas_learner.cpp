/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_farkas_learner.cpp

Abstract:

    Proviced abstract interface and some inplementations of algorithms
    for strenghtning lemmas

Author:

    Krystof Hoder (t-khoder) 2011-11-1.

Revision History:

--*/

#include "ast_smt2_pp.h"
#include "array_decl_plugin.h"
#include "bool_rewriter.h"
#include "dl_decl_plugin.h"
#include "for_each_expr.h"
#include "dl_util.h"
#include "rewriter.h"
#include "rewriter_def.h"
#include "spacer_util.h"
#include "spacer_farkas_learner.h"
#include "th_rewriter.h"
#include "ast_ll_pp.h"
#include "arith_bounds_tactic.h"
#include "proof_utils.h"
#include "reg_decl_plugins.h"
#include "smt_farkas_util.h"

namespace spacer {

    farkas_learner::farkas_learner(smt_params& params, ast_manager& outer_mgr) 
        : m_proof_params(get_proof_params(params)), 
          m_pr(PGM_FINE),
          m_split_literals (false),
          p2o(m_pr, outer_mgr),
          o2p(outer_mgr, m_pr)
    {
        reg_decl_plugins(m_pr);
        m_ctx = alloc(smt::kernel, m_pr, m_proof_params);
    }

    smt_params farkas_learner::get_proof_params(smt_params& orig_params) {
        smt_params res(orig_params);
        res.m_arith_bound_prop = BP_NONE;
        // temp hack to fix the build
        // res.m_conflict_resolution_strategy = CR_ALL_DECIDED;
        res.m_arith_auto_config_simplex = true;
        res.m_arith_propagate_eqs = false;
        res.m_arith_eager_eq_axioms = false;
        res.m_arith_eq_bounds = false;
        return res;
    }

    class farkas_learner::equality_expander_cfg : public default_rewriter_cfg
    {
        ast_manager& m;
        arith_util   m_ar;
    public:
        equality_expander_cfg(ast_manager& m) : m(m), m_ar(m) {}

        bool get_subst(expr * s, expr * & t, proof * & t_pr) {
            expr * x, *y;
            if (m.is_eq(s, x, y) && (m_ar.is_int(x) || m_ar.is_real(x))) {
                t = m.mk_and(m_ar.mk_ge(x, y), m_ar.mk_le(x, y));
                return true;
            }
            else {
                return false;
            }
        }
    };

    class collect_pure_proc {
        func_decl_set& m_symbs;
    public:
        collect_pure_proc(func_decl_set& s):m_symbs(s) {}

        void operator()(app* a) {
            if (a->get_family_id() == null_family_id) {
                m_symbs.insert(a->get_decl());
            }
        }
        void operator()(var*) {}
        void operator()(quantifier*) {}
    };


    bool farkas_learner::get_lemma_guesses(expr * A_ext, expr * B_ext, expr_ref_vector& lemmas)
    {
        expr_ref A(o2p(A_ext), m_pr);
        expr_ref B(o2p(B_ext), m_pr);
        proof_ref pr(m_pr);
        expr_ref tmp(m_pr);
        expr_ref_vector ilemmas(m_pr);
        equality_expander_cfg ee_rwr_cfg(m_pr);
        rewriter_tpl<equality_expander_cfg> ee_rwr(m_pr, false, ee_rwr_cfg);

        lemmas.reset();

        ee_rwr(A, A);
        ee_rwr(B, B);

        expr_set bs;
        expr_ref_vector blist(m_pr);
        flatten_and(B, blist);
        for (unsigned i = 0; i < blist.size(); ++i) {
            bs.insert(blist[i].get());
        }


        if (!m_ctx) {
            m_ctx = alloc(smt::kernel, m_pr, m_proof_params);
        }

        m_ctx->push();
        m_ctx->assert_expr(A);
        expr_set::iterator it = bs.begin(), end = bs.end();
        for (; it != end; ++it) {
            m_ctx->assert_expr(*it);
        }
        lbool res = m_ctx->check();
        bool is_unsat = res == l_false;
        if (is_unsat) {
            pr = m_ctx->get_proof();
            get_lemmas(m_ctx->get_proof(), bs, ilemmas);
            for (unsigned i = 0; i < ilemmas.size(); ++i) {
                lemmas.push_back(p2o(ilemmas[i].get()));
            }
        }
        m_ctx->pop(1);

        IF_VERBOSE(3, {
                for (unsigned i = 0; i < ilemmas.size(); ++i) {
                    verbose_stream() << "B': " << mk_pp(ilemmas[i].get(), m_pr) << "\n";
                }
            });

        TRACE("farkas_learner",
              tout << (is_unsat?"unsat":"sat") << "\n";
              tout << "A: " << mk_pp(A_ext, m_ctx->m()) << "\n";
              tout << "B: " << mk_pp(B_ext, m_ctx->m()) << "\n";
              for (unsigned i = 0; i < lemmas.size(); ++i) {
                  tout << "B': " << mk_pp(ilemmas[i].get(), m_pr) << "\n";
              });
        DEBUG_CODE(
            if (is_unsat) {
                m_ctx->push();
                m_ctx->assert_expr(A);
                for (unsigned i = 0; i < ilemmas.size(); ++i) {
                    m_ctx->assert_expr(ilemmas[i].get());
                }
                lbool res2 = m_ctx->check();
                SASSERT(l_false == res2);
                m_ctx->pop(1);
            }
            );
        return is_unsat;
    }

    //
    // Perform simple subsumption check of lemmas.
    //
    void farkas_learner::simplify_lemmas(expr_ref_vector& lemmas) {
        ast_manager& m = lemmas.get_manager();
        goal_ref g(alloc(goal, m, false, false, false));
        TRACE("farkas_simplify_lemmas",            
              for (unsigned i = 0; i < lemmas.size(); ++i) {
                  tout << mk_pp(lemmas[i].get(), m) << "\n";
              });

        for (unsigned i = 0; i < lemmas.size(); ++i) {
            g->assert_expr(lemmas[i].get()); 
        }
        expr_ref tmp(m);
        model_converter_ref mc;
        proof_converter_ref pc;
        expr_dependency_ref core(m);
        goal_ref_buffer result;
        tactic_ref simplifier = mk_arith_bounds_tactic(m);
        (*simplifier)(g, result, mc, pc, core);
        lemmas.reset();
        SASSERT(result.size() == 1);
        goal* r = result[0];
        for (unsigned i = 0; i < r->size(); ++i) {
            lemmas.push_back(r->form(i));
        }
        TRACE("farkas_simplify_lemmas", 
              tout << "simplified:\n";           
              for (unsigned i = 0; i < lemmas.size(); ++i) {
                  tout << mk_pp(lemmas[i].get(), m) << "\n";
              });
    }


    void farkas_learner::combine_constraints(unsigned n, app * const * lits, rational const * coeffs, expr_ref& res)
    {
        ast_manager& m = res.get_manager();
        smt::farkas_util res_c (m);
        res_c.set_split_literals (m_split_literals);
        for(unsigned i = 0; i < n; ++i) {
            res_c.add(coeffs[i], lits[i]);
        }
        res = res_c.get();
    }

    class farkas_learner::constant_replacer_cfg : public default_rewriter_cfg
    {
        const obj_map<expr, expr *>& m_translation;
    public:
        constant_replacer_cfg(const obj_map<expr, expr *>& translation)
            : m_translation(translation)
        { }

        bool get_subst(expr * s, expr * & t, proof * & t_pr) {
            return m_translation.find(s, t);
        }
    };

    // every uninterpreted symbol is in symbs
    class is_pure_expr_proc {
        func_decl_set const& m_symbs;
        array_util           m_au;
    public:
        struct non_pure {};

        is_pure_expr_proc(func_decl_set const& s, ast_manager& m):
            m_symbs(s),
            m_au (m)
        {}

        void operator()(app* a) {
            if (a->get_family_id() == null_family_id) {
                if (!m_symbs.contains(a->get_decl())) {
                    throw non_pure();
                }
            }
            else if (a->get_family_id () == m_au.get_family_id () &&
                     a->is_app_of (a->get_family_id (), OP_ARRAY_EXT)) {
                throw non_pure();
            }
        }
        void operator()(var*) {}
        void operator()(quantifier*) {}
    };

    bool farkas_learner::is_pure_expr(func_decl_set const& symbs, expr* e, ast_manager& m) const {
        is_pure_expr_proc proc(symbs, m);
        try {
            for_each_expr(proc, e);
        }
        catch (is_pure_expr_proc::non_pure) {
            return false;
        }
        return true;
    };


    /**
       Revised version of Farkas strengthener.
       1. Mark B-pure nodes as derivations that depend only on B.
       2. Collect B-influenced nodes
       3. (optional) Permute B-pure units over resolution steps to narrow dependencies on B.
       4. Weaken B-pure units for resolution with Farkas Clauses.
       5. Add B-pure units elsewhere.

       Rules:
       - hypothesis h |- h

                    H |- false
       - lemma      ----------
                     |- not H

                    Th |- L \/ C   H |- not L
       - th-lemma   -------------------------
                           H  |- C

         Note: C is false for theory axioms, C is unit literal for propagation.

       - rewrite        |- t = s

                        H |- t = s
       - monotonicity   ----------------
                       H |- f(t) = f(s)

                        H |- t = s H' |- s = u
       - trans          ----------------------
                            H, H' |- t = u

                        H |- C \/ L  H' |- not L
       - unit_resolve   ------------------------
                                H, H' |- C

                        H |- a ~ b   H' |- a
       - mp             --------------------
                             H, H' |- b

       - def-axiom       |- C
       
       - asserted        |- f

       Mark nodes by:
          - Hypotheses
          - Dependency on bs
          - Dependency on A

       A node is unit derivable from bs if:
          - It has no hypotheses.
          - It depends on bs.
          - It does not depend on A.

       NB: currently unit derivable is not symmetric: A clause can be 
       unit derivable, but a unit literal with hypotheses is not.
       This is clearly wrong, because hypotheses are just additional literals
       in a clausal version.

       NB: the routine is not interpolating, though an interpolating variant would 
       be preferrable because then we can also use it for model propagation.

       We collect the unit derivable nodes from bs.
       These are the weakenings of bs, besides the 
       units under Farkas.
                    
    */

#define INSERT(_x_) if (!lemma_set.contains(_x_)) { lemma_set.insert(_x_); lemmas.push_back(_x_); }

    void farkas_learner::get_lemmas(proof* root, expr_set const& bs, expr_ref_vector& lemmas) {
        ast_manager& m = lemmas.get_manager();
        bool_rewriter brwr(m);
        func_decl_set Bsymbs;
        collect_pure_proc collect_proc(Bsymbs);
        expr_set::iterator it = bs.begin(), end = bs.end();
        for (; it != end; ++it) {
            for_each_expr(collect_proc, *it);
        }

        proof_ref pr(root, m);
        proof_utils::reduce_hypotheses(pr);
        proof_utils::permute_unit_resolution(pr);
        IF_VERBOSE(3, verbose_stream() << "Reduced proof:\n" << mk_ismt2_pp(pr, m) << "\n";);
        
        ptr_vector<expr_set> hyprefs;
        obj_map<expr, expr_set*> hypmap;
        obj_hashtable<expr> lemma_set;
        ast_mark b_depend, a_depend, visited, b_closed;
        expr_set* empty_set = alloc(expr_set);
        hyprefs.push_back(empty_set); 
        ptr_vector<proof> todo;
        TRACE("spacer_verbose", tout << mk_pp(pr, m) << "\n";);
        todo.push_back(pr);
        while (!todo.empty()) {
            proof* p = todo.back();
            SASSERT(m.is_proof(p));
            if (visited.is_marked(p)) {
                todo.pop_back();
                continue;
            }
            bool all_visit = true;
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                expr* arg = p->get_arg(i);
                SASSERT(m.is_proof(arg));
                if (!visited.is_marked(arg)) {
                    all_visit = false;
                    todo.push_back(to_app(arg));
                }
            }
            if (!all_visit) {
                continue;
            }
            visited.mark(p, true);
            todo.pop_back();

            // retrieve hypotheses and dependencies on A, bs.
            bool b_dep = false, a_dep = false;
            expr_set* hyps = empty_set;
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                expr* arg = p->get_arg(i);
                a_dep = a_dep || a_depend.is_marked(arg);
                b_dep = b_dep || b_depend.is_marked(arg);
                expr_set* hyps2 = hypmap.find(arg);
                if (hyps != hyps2 && !hyps2->empty()) {
                    if (hyps->empty()) {
                        hyps = hyps2;
                    }
                    else {
                        expr_set* hyps3 = alloc(expr_set);
                        datalog::set_union(*hyps3, *hyps);
                        datalog::set_union(*hyps3, *hyps2);
                        hyps = hyps3;
                        hyprefs.push_back(hyps);
                    }
                }
            }
            hypmap.insert(p, hyps);
            a_depend.mark(p, a_dep);
            b_depend.mark(p, b_dep);

#define IS_B_PURE(_p) (b_depend.is_marked(_p) && !a_depend.is_marked(_p) && hypmap.find(_p)->empty())


            // Add lemmas that depend on bs, have no hypotheses, don't depend on A.
            if ((!hyps->empty() || a_depend.is_marked(p)) && 
                b_depend.is_marked(p) && !is_farkas_lemma(m, p)) {
                for (unsigned i = 0; i < m.get_num_parents(p); ++i) {                
                    app* arg = to_app(p->get_arg(i));
                    if (IS_B_PURE(arg)) {
                        expr* fact = m.get_fact(arg);
                        if (is_pure_expr(Bsymbs, fact, m)) {
                            TRACE("farkas_learner", 
                                  tout << "Add: " << mk_pp(m.get_fact(arg), m) << "\n";
                                  tout << mk_pp(arg, m) << "\n";
                                  );
                            INSERT(fact);
                        }
                        else {
                            get_asserted(p, bs, b_closed, lemma_set, lemmas);
                            b_closed.mark(p, true);
                        }
                    }
                }
            }
            
            switch(p->get_decl_kind()) {
            case PR_ASSERTED:
                if (bs.contains(m.get_fact(p))) {
                    b_depend.mark(p, true);
                }
                else {
                    a_depend.mark(p, true);
                }
                break;
            case PR_HYPOTHESIS: {
                SASSERT(hyps == empty_set);
                hyps = alloc(expr_set);
                hyps->insert(m.get_fact(p));
                hyprefs.push_back(hyps);
                hypmap.insert(p, hyps);
                break;
            }
            case PR_DEF_AXIOM: {
                if (!is_pure_expr(Bsymbs, m.get_fact(p), m)) {
                    a_depend.mark(p, true);
                }
                break;
            }
            case PR_LEMMA: {
                expr_set* hyps2 = alloc(expr_set);
                hyprefs.push_back(hyps2);
                datalog::set_union(*hyps2, *hyps); 
                hyps = hyps2;
                expr* fml = m.get_fact(p);
                hyps->remove(fml);
                if (m.is_or(fml)) {
                    for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
                        expr* f = to_app(fml)->get_arg(i);
                        expr_ref hyp(m);
                        brwr.mk_not(f, hyp);
                        hyps->remove(hyp);
                    }
                }
                hypmap.insert(p, hyps);
                break;
            }
            case PR_TH_LEMMA: {
                if (!is_farkas_lemma(m, p)) break;
               
                SASSERT(m.has_fact(p));
                unsigned prem_cnt = m.get_num_parents(p);
                func_decl * d = p->get_decl();
                SASSERT(d->get_num_parameters() >= prem_cnt+2);
                SASSERT(d->get_parameter(0).get_symbol() == "arith");
                SASSERT(d->get_parameter(1).get_symbol() == "farkas");
                parameter const* params = d->get_parameters() + 2;

                app_ref_vector lits(m);
                expr_ref tmp(m);
                unsigned num_b_pures = 0;
                rational coef;
                vector<rational> coeffs;

                TRACE("farkas_learner", 
                        for (unsigned i = 0; i < prem_cnt; ++i) {
                            VERIFY(params[i].is_rational(coef));
                            proof* prem = to_app(p->get_arg(i));
                            bool b_pure = IS_B_PURE(prem);
                            tout << (b_pure?"B":"A") << " " << coef << " " << mk_pp(m.get_fact(prem), m) << "\n";
                        }
                        tout << mk_pp(m.get_fact(p), m) << "\n";
                        );

                // NB. Taking 'abs' of coefficients is a workaround.
                // The Farkas coefficient extraction in arith_core must be wrong.
                // The coefficients would be always positive relative to the theory lemma.

                for(unsigned i = 0; i < prem_cnt; ++i) {                    
                    expr * prem_e = p->get_arg(i);
                    SASSERT(is_app(prem_e));
                    proof * prem = to_app(prem_e);
                   
                    if(IS_B_PURE(prem)) {
                        ++num_b_pures;
                    }
                    else {
                        VERIFY(params[i].is_rational(coef));
                        lits.push_back(to_app(m.get_fact(prem)));
                        coeffs.push_back(abs(coef));
                    }
                }
                params += prem_cnt;
                if (prem_cnt + 2 < d->get_num_parameters()) {
                    unsigned num_args = 1;
                    expr* fact = m.get_fact(p);
                    expr* const* args = &fact;
                    if (m.is_or(fact)) {
                        app* _or = to_app(fact);
                        num_args = _or->get_num_args();
                        args = _or->get_args();                        
                    }
                    SASSERT(prem_cnt + 2 + num_args == d->get_num_parameters());
                    for (unsigned i = 0; i < num_args; ++i) {
                        expr* prem_e = args[i];
                        brwr.mk_not(prem_e, tmp);
                        VERIFY(params[i].is_rational(coef));
                        SASSERT(is_app(tmp));
                        lits.push_back(to_app(tmp));
                        coeffs.push_back(abs(coef));
                    }

                }
                SASSERT(coeffs.size() == lits.size());
                if (num_b_pures > 0) {
                    expr_ref res(m);
                    combine_constraints(coeffs.size(), lits.c_ptr(), coeffs.c_ptr(), res);
                    TRACE("farkas_learner", tout << "Add: " << mk_pp(res, m) << "\n";);
                    INSERT(res);
                    b_closed.mark(p, true);
                }
            }
            default:
                break;
            }
        }

        std::for_each(hyprefs.begin(), hyprefs.end(), delete_proc<expr_set>());
        simplify_lemmas(lemmas);
    }

    void farkas_learner::get_asserted(proof* p, expr_set const& bs, ast_mark& b_closed, obj_hashtable<expr>& lemma_set, expr_ref_vector& lemmas) {
        ast_manager& m = lemmas.get_manager();
        ast_mark visited;
        proof* p0 = p;
        ptr_vector<proof> todo;        
        todo.push_back(p);
                      
        while (!todo.empty()) {
            p = todo.back();
            todo.pop_back();
            if (visited.is_marked(p) || b_closed.is_marked(p)) {
                continue;
            }
            visited.mark(p, true);
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                expr* arg = p->get_arg(i);
                SASSERT(m.is_proof(arg));
                todo.push_back(to_app(arg));
            }
            if (p->get_decl_kind() == PR_ASSERTED &&
                bs.contains(m.get_fact(p))) {
                expr* fact = m.get_fact(p);
                TRACE("farkas_learner", 
                      tout << mk_ll_pp(p0,m) << "\n";
                      tout << "Add: " << mk_pp(p,m) << "\n";);
                INSERT(fact);
                b_closed.mark(p, true);
            }
        }
    }


    bool farkas_learner::is_farkas_lemma(ast_manager& m, expr* e) {
        app * a;
        func_decl* d;
        symbol sym;
        return 
            is_app(e) && 
            (a = to_app(e), d = a->get_decl(), true) &&
            PR_TH_LEMMA == a->get_decl_kind() &&
            d->get_num_parameters() >= 2 &&
            d->get_parameter(0).is_symbol(sym) && sym == "arith" &&
            d->get_parameter(1).is_symbol(sym) && sym == "farkas" &&
            d->get_num_parameters() >= m.get_num_parents(to_app(e)) + 2;
    };


    void farkas_learner::test()  {
        smt_params params;
        enable_trace("farkas_learner");
               
        bool res;
        ast_manager m;
        reg_decl_plugins(m);        
        arith_util a(m);
        spacer::farkas_learner fl(params, m);
        expr_ref_vector lemmas(m);
        
        sort_ref int_s(a.mk_int(), m);
        expr_ref x(m.mk_const(symbol("x"), int_s), m);
        expr_ref y(m.mk_const(symbol("y"), int_s), m);
        expr_ref z(m.mk_const(symbol("z"), int_s), m);    
        expr_ref u(m.mk_const(symbol("u"), int_s), m);  
        expr_ref v(m.mk_const(symbol("v"), int_s), m);

        // A: x > y >= z
        // B: x < z
        // Farkas: x <= z
        expr_ref A(m.mk_and(a.mk_gt(x,y), a.mk_ge(y,z)),m);        
        expr_ref B(a.mk_gt(z,x),m);        
        res = fl.get_lemma_guesses(A, B, lemmas);        
        std::cout << "\nres: " << res << "\nlemmas: " << pp_cube(lemmas, m) << "\n";

        // A: x > y >= z + 2
        // B: x = 1, z = 8
        // Farkas: x <= z + 2
        expr_ref one(a.mk_numeral(rational(1), true), m);
        expr_ref two(a.mk_numeral(rational(2), true), m);
        expr_ref eight(a.mk_numeral(rational(8), true), m);
        A = m.mk_and(a.mk_gt(x,y),a.mk_ge(y,a.mk_add(z,two)));
        B = m.mk_and(m.mk_eq(x,one), m.mk_eq(z, eight));
        res = fl.get_lemma_guesses(A, B, lemmas);        
        std::cout << "\nres: " << res << "\nlemmas: " << pp_cube(lemmas, m) << "\n";

        // A: x > y >= z \/ x >= u > z
        // B: z > x + 1
        // Farkas: z >= x
        A = m.mk_or(m.mk_and(a.mk_gt(x,y),a.mk_ge(y,z)),m.mk_and(a.mk_ge(x,u),a.mk_gt(u,z)));
        B = a.mk_gt(z, a.mk_add(x,one));
        res = fl.get_lemma_guesses(A, B, lemmas);        
        std::cout << "\nres: " << res << "\nlemmas: " << pp_cube(lemmas, m) << "\n";

        // A: (x > y >= z \/ x >= u > z \/ u > v)
        // B: z > x + 1 & not (u > v)
        // Farkas: z >= x & not (u > v)
        A = m.mk_or(m.mk_and(a.mk_gt(x,y),a.mk_ge(y,z)),m.mk_and(a.mk_ge(x,u),a.mk_gt(u,z)), a.mk_gt(u, v));
        B = m.mk_and(a.mk_gt(z, a.mk_add(x,one)), m.mk_not(a.mk_gt(u, v)));
        res = fl.get_lemma_guesses(A, B, lemmas);        
        std::cout << "\nres: " << res << "\nlemmas: " << pp_cube(lemmas, m) << "\n";
        
    }

    void farkas_learner::collect_statistics(statistics& st) const {
        if (m_ctx) {
            m_ctx->collect_statistics(st);
        }
    }


};

