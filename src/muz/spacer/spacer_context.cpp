/** 
Spacer
Copyright (c) 2015 Carnegie Mellon University.
All Rights Reserved.

THIS SOFTWARE IS PROVIDED "AS IS," WITH NO WARRANTIES
WHATSOEVER. CARNEGIE MELLON UNIVERSITY EXPRESSLY DISCLAIMS TO THE
FULLEST EXTENT PERMITTEDBY LAW ALL EXPRESS, IMPLIED, AND STATUTORY
WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND
NON-INFRINGEMENT OF PROPRIETARY RIGHTS.

Released under a modified MIT license, please see SPACER_LICENSE.txt
for full terms.  DM-0002483

Spacer includes and/or makes use of the following Third-Party Software
subject to its own license:

Z3
Copyright (c) Microsoft Corporation
All rights reserved.

Released under the MIT License (LICENSE.txt)

Module Name:

    spacer_context.cpp

Abstract:

    SPACER predicate transformers and search context.

Author:

    Arie Gurfinkel
    Anvesh Komuravelli

    Based on muz/pdr/pdr_context.cpp by Nikolaj Bjorner (nbjorner)

Notes:
   
--*/


#include <sstream>
#include "dl_util.h"
#include "rewriter.h"
#include "rewriter_def.h"
#include "var_subst.h"
#include "util.h"
#include "spacer_prop_solver.h"
#include "spacer_context.h"
#include "spacer_generalizers.h"
#include "for_each_expr.h"
#include "dl_rule_set.h"
#include "unit_subsumption_tactic.h"
#include "model_smt2_pp.h"
#include "dl_mk_rule_inliner.h"
#include "ast_smt2_pp.h"
#include "ast_ll_pp.h"
#include "proof_checker.h"
#include "smt_value_sort.h"
#include "proof_utils.h"
#include "scoped_proof.h"
#include "qe_project.h"
#include "blast_term_ite_tactic.h"

#include "timeit.h"
#include "luby.h"

namespace spacer {
    
    // ----------------
    // pred_tansformer

    pred_transformer::pred_transformer(context& ctx, manager& pm, func_decl* head): 
        pm(pm), m(pm.get_manager()),
        ctx(ctx), m_head(head, m), 
        m_sig(m), m_solver(pm, ctx.get_params(), head->get_name(), ctx.get_params ().validate_theory_core ()),
        m_reach_ctx (pm.mk_fresh ()),
        m_frames (*this), 
        m_reach_facts (), m_rf_init_sz (0),
        m_transition(m), m_initial_state(m), m_extend_lit (m),
        m_all_init (false),
        m_reach_case_vars (m)
    {
      init_sig ();
      app_ref v(m);
      v = m.mk_fresh_const (m_head->get_name ().str ().c_str (),
                            m.mk_bool_sort ());
      m_extend_lit = m.mk_not (m.mk_const (pm.get_n_pred (v->get_decl ())));
    }

    pred_transformer::~pred_transformer() {
        rule2inst::iterator it2 = m_rule2inst.begin(), end2 = m_rule2inst.end();
        for (; it2 != end2; ++it2) {
            dealloc(it2->m_value);
        }
        rule2expr::iterator it3 = m_rule2transition.begin(), end3 = m_rule2transition.end();
        for (; it3 != end3; ++it3) {
            m.dec_ref(it3->m_value);
        }
    }

    std::ostream& pred_transformer::display(std::ostream& out) const {
        if (!rules().empty()) out << "rules\n";
        datalog::rule_manager& rm = ctx.get_datalog_context().get_rule_manager();
        for (unsigned i = 0; i < rules().size(); ++i) {
            rm.display_smt2(*rules()[i], out) << "\n";
        }        
        out << "transition\n" << mk_pp(transition(), m) << "\n";
        return out;
    }

    void pred_transformer::collect_statistics(statistics& st) const {
        m_solver.collect_statistics(st);
        //m_reachable.collect_statistics(st);
        st.update("SPACER num propagations", m_stats.m_num_propagations);
        st.update("SPACER num properties", m_frames.lemma_size ()); 
    }

    void pred_transformer::reset_statistics() {
        m_solver.reset_statistics();
        //m_reachable.reset_statistics();
        m_stats.reset();
    }
    
    void pred_transformer::init_sig() {
        for (unsigned i = 0; i < m_head->get_arity(); ++i) {
            sort * arg_sort = m_head->get_domain(i);
            std::stringstream name_stm;
            name_stm << m_head->get_name() << '_' << i;
            func_decl_ref stm(m);
            stm = m.mk_func_decl(symbol(name_stm.str().c_str()), 0, (sort*const*)0, arg_sort);
            m_sig.push_back(pm.get_o_pred(stm, 0));       
        }
    }

    void pred_transformer::ensure_level(unsigned level) {
        if (is_infty_level(level)) return;
        
        while (m_frames.size () <= level)
        {
          m_frames.add_frame ();
          m_solver.add_level ();
        }
    }

    bool pred_transformer::is_must_reachable (expr* state, model_ref* model) {
        SASSERT (state);
        // XXX This seems to mis-handle the case when state is
        // reachable using the init rule of the current transformer
        if (m_reach_facts.empty ()) return false;
        
        m_reach_ctx->push ();
        m_reach_ctx->assert_expr (state);
        m_reach_ctx->assert_expr (m.mk_not (m_reach_case_vars.back ()));
        expr_ref_vector assumptions (m);
        lbool res = m_reach_ctx->check (assumptions);
        if (model) m_reach_ctx->get_model (*model);
        m_reach_ctx->pop ();
        return (res == l_true);
    }

  
  expr_ref pred_transformer::eval (model_evaluator &mev, expr * v)
  {
    expr_ref res(m);
    if (ctx.get_params ().use_heavy_mev ()) 
      res = mev.eval_heavy (v);
    else 
      res = mev.eval (v);
    return res;
  }
  
  reach_fact* pred_transformer::get_used_reach_fact (model_evaluator& mev,
                                                     bool all) {
    expr_ref v (m);
    
    for (unsigned i = all ? 0 : m_rf_init_sz, sz = m_reach_case_vars.size ();
         i < sz; i++) {
      v = mev.eval (m_reach_case_vars.get (i));
      if (m.is_false (v)) {
        return m_reach_facts.get (i);
      }
    }
    
    UNREACHABLE ();
    return NULL;
  }
  
  reach_fact *pred_transformer::get_used_origin_reach_fact (model_evaluator& mev, 
                                                            unsigned oidx) {
    expr_ref b(m), v(m);
    reach_fact *res = NULL;
    
    for (unsigned i = 0, sz = m_reach_case_vars.size (); i < sz; i++) {
      pm.formula_n2o (m_reach_case_vars.get (i), v, oidx);
      b = mev.eval (v);
      
      if (m.is_false (b)) {
        res = m_reach_facts.get (i);
        break;
      }
    }
    SASSERT (res);
    return res;
  }

    datalog::rule const* pred_transformer::find_rule(model &model, 
                                                     bool& is_concrete, 
                                                     vector<bool>& reach_pred_used, 
                                                     unsigned& num_reuse_reach) {
        typedef obj_map<expr, datalog::rule const*> tag2rule;
        TRACE ("spacer_verbose",
                datalog::rule_manager& rm = ctx.get_datalog_context().get_rule_manager();
                tag2rule::iterator it = m_tag2rule.begin();
                tag2rule::iterator end = m_tag2rule.end();
                for (; it != end; ++it) {
                    expr* pred = it->m_key;
                    tout << mk_pp(pred, m) << ":\n";
                    if (it->m_value) rm.display_smt2 (*(it->m_value), tout) << "\n";
                }
              );

        // find a rule whose tag is true in the model;
        // prefer a rule where the model intersects with reach facts of all predecessors;
        // also find how many predecessors' reach facts are true in the model
        expr_ref vl(m);
        datalog::rule const* r = ((datalog::rule*)0);
        tag2rule::iterator it = m_tag2rule.begin(), end = m_tag2rule.end();
        for (; it != end; ++it) {
            expr* tag = it->m_key;
            if (model.eval(to_app(tag)->get_decl(), vl) && m.is_true(vl)) {
                r = it->m_value;
                is_concrete = true;
                num_reuse_reach = 0;
                reach_pred_used.reset ();
                unsigned tail_sz = r->get_uninterpreted_tail_size ();
                for (unsigned i = 0; i < tail_sz; i++) {
                    bool used = false;
                    func_decl* d = r->get_tail(i)->get_decl();
                    pred_transformer const& pt = ctx.get_pred_transformer (d);
                    if (!pt.has_reach_facts ()) is_concrete = false;
                    else {
                      expr_ref v(m);
                      pm.formula_n2o (pt.get_last_reach_case_var (), v, i);
                      model.eval (to_app (v.get ())->get_decl (), vl);
                      used = m.is_false (vl);
                      is_concrete = is_concrete && used;
                    }

                    reach_pred_used.push_back (used);
                    if (used) num_reuse_reach++;
                }
                if (is_concrete) break;
            }
        }
        // SASSERT (r);
        // reached by a reachability fact
        if (!r) is_concrete = true;
        return r;
    }

    void pred_transformer::find_predecessors(datalog::rule const& r, ptr_vector<func_decl>& preds) const {
        preds.reset();
        unsigned tail_sz = r.get_uninterpreted_tail_size();
        for (unsigned ti = 0; ti < tail_sz; ti++) {
            preds.push_back(r.get_tail(ti)->get_decl());
        }
    }

    void pred_transformer::find_predecessors(vector<std::pair<func_decl*, unsigned> >& preds) const {
        preds.reset();
        obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin(), end = m_tag2rule.end();
        for (; it != end; it++) {
            datalog::rule const& r = *it->m_value;
            unsigned tail_sz = r.get_uninterpreted_tail_size();
            for (unsigned ti = 0; ti < tail_sz; ti++) {
                preds.push_back(std::make_pair (r.get_tail(ti)->get_decl(), ti));
            }
        }
    }


    void pred_transformer::remove_predecessors(expr_ref_vector& literals) {
        // remove tags
        for (unsigned i = 0; i < literals.size(); ) {
            expr* l = literals[i].get();
            m.is_not(l, l);
            if (m_tag2rule.contains(l)) {
                literals[i] = literals.back();
                literals.pop_back();
            }
            else {
                ++i;
            }
        }
    }

    void pred_transformer::simplify_formulas() {
      m_frames.simplify_formulas ();
    }

  
    expr_ref pred_transformer::get_formulas(unsigned level, bool add_axioms) {
        expr_ref_vector res(m);
        if (add_axioms) {
            res.push_back(pm.get_background());
            res.push_back((level == 0)?initial_state():transition());
        }
        m_frames.get_frame_geq_lemmas (level, res);
        return pm.mk_and(res);
    }

    expr_ref pred_transformer::get_propagation_formula(decl2rel const& pts, unsigned level) {
        expr_ref result(m), tmp1(m), tmp2(m);
        expr_ref_vector conj(m);
        if (level == 0) {
            conj.push_back(initial_state());
        }
        else {
            conj.push_back(transition());
        }
        conj.push_back(get_formulas(level, true));        
        obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin(), end = m_tag2rule.end();
        for (; level > 0 && it != end; ++it) {
            expr* tag = it->m_key;
            datalog::rule const* r = it->m_value;
            if (!r) continue;
            find_predecessors(*r, m_predicates);
            for (unsigned i = 0; i < m_predicates.size(); ++i) {
                func_decl* d = m_predicates[i];
                pred_transformer & pt = *pts.find(d);
                tmp1 = pt.get_formulas(level-1, false);
                TRACE("spacer", tout << mk_pp(tmp1, m) << "\n";);
                pm.formula_n2o(tmp1, tmp2, i, false);
                conj.push_back(m.mk_implies(tag, tmp2));
            }
        }                  
        return pm.mk_and(conj);
    }

  bool pred_transformer::propagate_to_next_level (unsigned src_level)
  {return m_frames.propagate_to_next_level (src_level);}
  

  /// \brief adds a lemma to the solver and to child solvers
  void pred_transformer::add_lemma_core (expr * lemma, unsigned lvl)
  {
    TRACE("spacer", tout << "add-lemma-core: " << pp_level (lvl)
          << " " << head ()->get_name () 
          << " " << mk_pp (lemma, m) << "\n";);
    
    TRACE("core_array_eq", tout << "add-lemma-core: " << pp_level (lvl)
          << " " << head ()->get_name () 
          << " " << mk_pp (lemma, m) << "\n";);
    
    if (is_infty_level (lvl)) m_solver.add_formula (lemma);
    else 
    {
      ensure_level (lvl);
      m_solver.add_level_formula (lemma, lvl);
    }
    
    for (unsigned i = 0, sz = m_use.size (); i < sz; ++i)
      m_use [i]->add_lemma_from_child (*this, lemma, next_level (lvl));
  }
  
  bool pred_transformer::add_lemma (expr * lemma, unsigned lvl)
  {
    bool res = false;
    
    expr_ref_vector lemmas (m);
    qe::flatten_and (lemma, lemmas);
    for (unsigned i = 0, sz = lemmas.size(); i < sz; ++i)
      res |= m_frames.add_lemma (lemmas.get (i), lvl);
    return res;
  }
  

  void pred_transformer::add_lemma_from_child (pred_transformer& child, 
                                               expr* lemma, unsigned lvl) 
  {
    ensure_level(lvl);
    expr_ref_vector fmls(m);
    mk_assumptions(child.head(), lemma, fmls);
    for (unsigned i = 0; i < fmls.size(); ++i) {
      TRACE("spacer_detail", tout << "child property: " 
            << mk_pp(fmls.get (i), m) << "\n";);
      if (is_infty_level(lvl)) 
        m_solver.add_formula(fmls.get (i));
      else 
        m_solver.add_level_formula(fmls.get (i), lvl);
    }
  }

    expr* pred_transformer::mk_fresh_reach_case_var () 
    {
      std::stringstream name;
      func_decl_ref decl(m);
        
      name << head ()->get_name () << "#reach_case_" << m_reach_case_vars.size ();
      decl = m.mk_func_decl (symbol (name.str ().c_str ()), 0, 
                             (sort*const*)0, m.mk_bool_sort ());
      m_reach_case_vars.push_back (m.mk_const (pm.get_n_pred (decl)));
      return m_reach_case_vars.back ();
    }

    expr* pred_transformer::get_reach_case_var (unsigned idx) const 
    {return m_reach_case_vars.get (idx);}


  void pred_transformer::add_reach_fact (reach_fact &fact) 
    {
      timeit _timer (is_trace_enabled("spacer_timeit"), 
                     "spacer::pred_transformer::add_reach_fact", 
                     verbose_stream ());

      TRACE ("spacer",
             tout << "add_reach_fact: " << head()->get_name() << " " 
             << (fact.is_init () ? "INIT " : "")
             << mk_pp(fact.get (), m) << "\n";);
      
      // -- avoid duplicates
      if (get_reach_fact (fact.get ())) return;

      // all initial facts are grouped together
      SASSERT (!fact.is_init () || m_reach_facts.empty () ||
               m_reach_facts.back ()->is_init ());
      
      m_reach_facts.push_back (&fact);
      if (fact.is_init ()) m_rf_init_sz++;
      

      // update m_reach_ctx
      expr_ref last_var (m);
      expr_ref new_var (m);
      expr_ref fml (m);
      
      if (!m_reach_case_vars.empty ()) last_var = m_reach_case_vars.back ();
      if (fact.is_init () || !ctx.get_params ().spacer_reach_as_init ())
        new_var = mk_fresh_reach_case_var ();
      else
      {
        new_var = extend_initial (fact.get ())->get_arg (0);
        m_reach_case_vars.push_back (new_var);
      }
      
      SASSERT (m_reach_facts.size () == m_reach_case_vars.size ());
      
      if (last_var)
        fml = m.mk_or (m.mk_not (last_var), fact.get (), new_var);
      else
        fml = m.mk_or (fact.get (), new_var);
      
      m_reach_ctx->assert_expr (fml);
      TRACE ("spacer",
             tout << "updating reach ctx: " << mk_pp(fml, m) << "\n";);

      // update users; reach facts are independent of levels
      for (unsigned i = 0; i < m_use.size(); ++i) {
        m_use[i]->add_lemma_from_child (*this, fml, infty_level ());
      }
    }

    expr* pred_transformer::get_reach () {
        if (m_reach_facts.empty ()) {
            return m.mk_false ();
        }
        ptr_vector<expr> v;
        for (unsigned i = 1, sz = m_reach_facts.size (); i < sz; ++i)
          v.push_back (m_reach_facts[i]->get ());
        
        return m.mk_or (v.size (), v.c_ptr ());
    }

  expr* pred_transformer::get_last_reach_case_var () const 
  {
    return m_reach_case_vars.empty () ? NULL : m_reach_case_vars.back ();
  }
  
    expr_ref pred_transformer::get_cover_delta(func_decl* p_orig, int level) {
        expr_ref result(m.mk_true(), m), v(m), c(m);
        
        expr_ref_vector lemmas (m);
        m_frames.get_frame_lemmas (level == -1 ? infty_level() : level, lemmas);
        if (!lemmas.empty ()) result = pm.mk_and (lemmas);
        
        // replace local constants by bound variables.
        expr_substitution sub(m);        
        for (unsigned i = 0; i < sig_size(); ++i) {
            c = m.mk_const(pm.o2n(sig(i), 0));
            v = m.mk_var(i, sig(i)->get_range());
            sub.insert(c, v);
        }
        scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
        rep->set_substitution(&sub);
        (*rep)(result);

        // adjust result according to model converter.
        unsigned arity = m_head->get_arity();
        model_ref md = alloc(model, m);
        if (arity == 0) {
            md->register_decl(m_head, result);
        }
        else {
            func_interp* fi = alloc(func_interp, m, arity);
            fi->set_else(result);
            md->register_decl(m_head, fi);
        }
        model_converter_ref mc = ctx.get_model_converter();
        apply(mc, md, 0);
        if (p_orig->get_arity() == 0) {
            result = md->get_const_interp(p_orig);
        }
        else {
            result = md->get_func_interp(p_orig)->get_interp();
        }
        return result;        
    }

  /**
   * get an origin summary used by this transformer in the given model
   * level is the level at which may summaries are obtained
   * oidx is the origin index of this predicate in the model
   * must indicates whether a must or a may summary is requested
   *
   * returns an implicant of the summary
   */
  expr_ref pred_transformer::get_origin_summary (model_evaluator &mev, 
                                                 unsigned level, 
                                                 unsigned oidx,
                                                 bool must,
                                                 const ptr_vector<app> **aux)
  {
    expr_ref_vector summary (m);
    expr_ref v(m);
    
    if (!must) // use may summary
    {
      summary.push_back (get_formulas (level, false));
      // -- no auxiliary variables in lemmas
      *aux = NULL;
    }
    else // find must summary to use
    {
      reach_fact *f = get_used_origin_reach_fact (mev, oidx);
      summary.push_back (f->get ());
      *aux = &f->aux_vars ();
    }
    
    SASSERT (!summary.empty ());

    // -- convert to origin
    for (unsigned i = 0; i < summary.size (); ++i)
    {
      pm.formula_n2o (summary.get (i), v, oidx);
      summary[i] = v;
    }
    
    // -- pick an implicant
    expr_ref_vector literals (m);
    compute_implicant_literals (mev, summary, literals);
    
    return get_manager ().mk_and (literals);
  }
  

    void pred_transformer::add_cover(unsigned level, expr* property) {
        // replace bound variables by local constants.
        expr_ref result(property, m), v(m), c(m);
        expr_substitution sub(m);        
        for (unsigned i = 0; i < sig_size(); ++i) {
            c = m.mk_const(pm.o2n(sig(i), 0));
            v = m.mk_var(i, sig(i)->get_range());
            sub.insert(v, c);
        }
        scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
        rep->set_substitution(&sub);
        (*rep)(result);
        TRACE("spacer", tout << "cover:\n" << mk_pp(result, m) << "\n";);
        // add the property.
        add_lemma (result, level);        
    }

    void pred_transformer::propagate_to_infinity (unsigned level)
    {m_frames.propagate_to_infinity (level);}
  
      

  /// \brief Returns true if the obligation is already blocked by current lemmas
  bool pred_transformer::is_blocked (model_node &n, unsigned &uses_level)
  {
    ensure_level (n.level ());
    prop_solver::scoped_level _sl (m_solver, n.level ());
    m_solver.set_core (NULL);
    m_solver.set_model (NULL);

    expr_ref_vector post(m), aux(m);
    post.push_back (n.post ());
    lbool res = m_solver.check_assumptions (post, aux);
    if (res == l_false) uses_level = m_solver.uses_level ();
    return res == l_false;
  }
  
  lbool pred_transformer::is_reachable(model_node& n, expr_ref_vector* core, 
                                       model_ref* model, unsigned& uses_level, 
                                         bool& is_concrete, datalog::rule const*& r, 
                                       vector<bool>& reach_pred_used, 
                                       unsigned& num_reuse_reach) {
        TRACE("spacer", 
              tout << "is-reachable: " << head()->get_name() << " level: " 
              << n.level() << " depth: " << n.depth () << "\n";
              tout << mk_pp(n.post(), m) << "\n";);
        timeit _timer (is_trace_enabled("spacer_timeit"), 
                     "spacer::pred_transformer::is_reachable", 
                     verbose_stream ());

        ensure_level(n.level());        

        // prepare the solver
        prop_solver::scoped_level _sl(m_solver, n.level());
        prop_solver::scoped_subset_core _sc (m_solver, !n.use_farkas_generalizer ());
        m_solver.set_core(core);
        m_solver.set_model(model);

        expr_ref_vector post (m), reach_assumps (m);
        post.push_back (n.post ());

        // populate reach_assumps 

        // XXX eager_reach_check must always be
        // XXX enabled. Otherwise, we can get into an infinite loop in
        // XXX which a model is consistent with a must-summary, but the
        // XXX appropriate assumption is not set correctly by the model.
        // XXX Original code handled reachability-events differently.
        if (/* ctx.get_params ().eager_reach_check () && */
            n.level () > 0 && !m_all_init) {
            obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin (),
                end = m_tag2rule.end ();
            for (; it != end; ++it) {
                datalog::rule const* r = it->m_value;
                if (!r) continue;
                find_predecessors(*r, m_predicates);
                if (m_predicates.empty ()) continue;
                for (unsigned i = 0; i < m_predicates.size(); i++) {
                    const pred_transformer &pt = 
                      ctx.get_pred_transformer (m_predicates [i]);
                    if (pt.has_reach_facts ())
                    {
                      expr_ref a(m);
                      pm.formula_n2o (pt.get_last_reach_case_var (), a, i);
                      reach_assumps.push_back (m.mk_not (a));
                    }
                    else if (ctx.get_params ().init_reach_facts ())
                    {
                      reach_assumps.push_back (m.mk_not (it->m_key));
                      break;
                    }
                }
            }
        }

        TRACE ("spacer",
                if (!reach_assumps.empty ()) {
                    tout << "reach assumptions\n";
                    for (unsigned i = 0; i < reach_assumps.size (); i++) {
                        tout << mk_pp (reach_assumps.get (i), m) << "\n";
                    }
                }
              );

        // check local reachability;
        // result is either sat (with some reach assumps) or
        // unsat (even with no reach assumps)
        expr *bg = m_extend_lit.get ();
        lbool is_sat = m_solver.check_assumptions (post, reach_assumps, 1, &bg);

        TRACE ("spacer",
                if (!reach_assumps.empty ()) {
                    tout << "reach assumptions used\n";
                    for (unsigned i = 0; i < reach_assumps.size (); i++) {
                        tout << mk_pp (reach_assumps.get (i), m) << "\n";
                    }
                }
              );

        if (is_sat == l_true && core) {
            core->reset();
            SASSERT ((bool)model);
            r = find_rule (**model, is_concrete, reach_pred_used, num_reuse_reach);
            TRACE ("spacer", tout << "reachable "
                   << "is_concrete " << is_concrete << " rused: ";
                   for (unsigned i = 0, sz = reach_pred_used.size (); i < sz; ++i)
                     tout << reach_pred_used [i];
                   tout << "\n";);
            
            return l_true;
        }
        if (is_sat == l_false) {
            SASSERT (reach_assumps.empty ());
            TRACE ("spacer", tout << "unreachable with lemmas\n";
                    if (core) {
                        tout << "Core:\n";
                        for (unsigned i = 0; i < core->size (); i++) {
                            tout << mk_pp (core->get(i), m) << "\n";
                        }
                    }
                   );
            uses_level = m_solver.uses_level();
            return l_false;
        }
        return l_undef;
    }

    bool pred_transformer::is_invariant(unsigned level, expr* states,
                                        unsigned& solver_level, expr_ref_vector* core) {
      expr_ref_vector conj(m), aux(m);
        
        conj.push_back(m.mk_not(states));
        qe::flatten_and (conj);

        prop_solver::scoped_level _sl(m_solver, level);
        m_solver.set_core(core);
        m_solver.set_model(0);
        expr * bg = m_extend_lit.get ();
        lbool r = m_solver.check_assumptions (conj, aux, 1, &bg);
        if (r == l_false) {
            solver_level = m_solver.uses_level ();
            CTRACE ("spacer", level < m_solver.uses_level (), 
                    tout << "Checking at level " << level 
                    << " but only using " << m_solver.uses_level () << "\n";);
            SASSERT (level <= solver_level);
        }
        return r == l_false;
    }

    bool pred_transformer::check_inductive(unsigned level, expr_ref_vector& lits, 
                                           unsigned& uses_level) {
        manager& pm = get_manager();
        expr_ref_vector conj(m), core(m);
        expr_ref states(m);
        states = m.mk_not(pm.mk_and(lits));
        mk_assumptions(head(), states, conj);
        prop_solver::scoped_level _sl(m_solver, level);
        prop_solver::scoped_subset_core _sc (m_solver, true);
        m_solver.set_core(&core);
        expr_ref_vector aux (m);
        conj.push_back (m_extend_lit);
        lbool res = m_solver.check_assumptions (lits, aux, conj.size (), conj.c_ptr ());
        if (res == l_false) {
            lits.reset();
            lits.append(core);
            uses_level = m_solver.uses_level();
        }
        TRACE ("core_array_eq", 
               tout << "check_inductive: " 
               << "states: " << mk_pp (states, m) 
               << " is: " << res << "\n"
               << "with transition: " << mk_pp (m_transition, m) << "\n";);
        return res == l_false;
    }

    void pred_transformer::mk_assumptions(func_decl* head, expr* fml, 
                                          expr_ref_vector& result) {
        expr_ref tmp1(m), tmp2(m);
        expr_substitution sub (m);
        proof_ref pr (m.mk_asserted (m.mk_true ()), m);
        obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin(), 
          end = m_tag2rule.end();
        for (; it != end; ++it) {
            expr* tag = it->m_key;
            datalog::rule const* r = it->m_value;
            if (!r) continue;
            find_predecessors(*r, m_predicates);
            for (unsigned i = 0; i < m_predicates.size(); i++) {
                func_decl* d = m_predicates[i];
                if (d == head) {
                    tmp1 = m.mk_implies(tag, fml);
                    pm.formula_n2o(tmp1, tmp2, i);
                    result.push_back(tmp2);
                }
            }                  
        }
    }

    void pred_transformer::initialize(decl2rel const& pts) {
        m_initial_state = m.mk_false();
        m_transition = m.mk_true();        
        init_rules(pts, m_initial_state, m_transition);
        th_rewriter rw(m);
        rw(m_transition);
        rw(m_initial_state);
        
        m_solver.add_formula(m_transition);
        m_solver.add_level_formula(m_initial_state, 0);
        TRACE("spacer", 
              tout << "Initial state: " << mk_pp(m_initial_state, m) << "\n";
              tout << "Transition:    " << mk_pp(m_transition,  m) << "\n";);
        SASSERT(is_app(m_initial_state));
        //m_reachable.add_init(to_app(m_initial_state));
        

    }
  
    void pred_transformer::init_reach_facts ()
    {
      expr_ref_vector v(m);
      reach_fact *fact;

      rule2expr::iterator it = m_rule2tag.begin (), end = m_rule2tag.end ();
      for (; it != end; ++it)
      {
        const datalog::rule* r = it->m_key;
        if (r->get_uninterpreted_tail_size () == 0)
        {
          fact = alloc (reach_fact, m, *r, m_rule2transition.find (r),
                        get_aux_vars (*r), true);
          add_reach_fact (*fact);
        }
      }
    }
  
    void pred_transformer::init_rules(decl2rel const& pts, expr_ref& init, expr_ref& transition) {
        expr_ref_vector transitions(m);
        ptr_vector<datalog::rule const> tr_rules;
        datalog::rule const* rule;
        expr_ref_vector disj(m), init_conds (m);
        app_ref pred(m);
        vector<bool> is_init;
        for (unsigned i = 0; i < rules().size(); ++i) {
            init_rule(pts, *rules()[i], is_init, tr_rules, transitions);
        }
        SASSERT (is_init.size () == transitions.size ());
        switch(transitions.size()) {
        case 0:
            transition = m.mk_false(); 
            break;
        case 1:
            // create a dummy tag.
            pred = m.mk_fresh_const(head()->get_name().str().c_str(), m.mk_bool_sort());
            rule = tr_rules[0];
            m_tag2rule.insert(pred, rule);
            m_rule2tag.insert(rule, pred.get());            
            transitions [0] = m.mk_implies (pred, transitions.get (0));
            transitions.push_back (m.mk_or (pred, m_extend_lit->get_arg (0)));
            if (!is_init [0]) init_conds.push_back (m.mk_not (pred));
            
            transition = pm.mk_and(transitions);
            break;
        default:
            disj.push_back (m_extend_lit->get_arg (0));
            for (unsigned i = 0; i < transitions.size(); ++i) {
                pred = m.mk_fresh_const(head()->get_name().str().c_str(), m.mk_bool_sort());
                rule = tr_rules[i];
                m_tag2rule.insert(pred, rule);                   
                m_rule2tag.insert(rule, pred);                
                disj.push_back(pred);
                transitions[i] = m.mk_implies(pred, transitions[i].get());
                // update init conds
                if (!is_init[i]) {
                    init_conds.push_back (m.mk_not (pred));
                }
            }
            transitions.push_back(m.mk_or(disj.size(), disj.c_ptr()));
            transition = pm.mk_and(transitions);
            break;                 
        }
        // mk init condition
        init = pm.mk_and (init_conds);
        if (init_conds.empty ()) { // no rule has uninterpreted tail
            m_all_init = true;
        }
    }

    void pred_transformer::init_rule(
        decl2rel const&      pts,
        datalog::rule const& rule, 
        vector<bool>&     is_init, 
        ptr_vector<datalog::rule const>& rules,
        expr_ref_vector&     transitions) 
    {
        // Predicates that are variable representatives. Other predicates at 
        // positions the variables occur are made equivalent with these.
        expr_ref_vector conj(m);
        app_ref_vector& var_reprs = *(alloc(app_ref_vector, m));
        ptr_vector<app> aux_vars;
                
        unsigned ut_size = rule.get_uninterpreted_tail_size();
        unsigned t_size  = rule.get_tail_size();   
        SASSERT(ut_size <= t_size);
        init_atom(pts, rule.get_head(), var_reprs, conj, UINT_MAX);
        for (unsigned i = 0; i < ut_size; ++i) {
            if (rule.is_neg_tail(i)) {
                throw default_exception("SPACER does not support negated predicates in rule tails");
            }
            init_atom(pts, rule.get_tail(i), var_reprs, conj, i);
        }                  
        for (unsigned i = ut_size; i < t_size; ++i) {
          ground_free_vars(rule.get_tail(i), var_reprs, aux_vars, ut_size == 0);
        }
        SASSERT(check_filled(var_reprs));
        expr_ref_vector tail(m);
        for (unsigned i = ut_size; i < t_size; ++i) {
            tail.push_back(rule.get_tail(i));
        }        
        qe::flatten_and(tail);
        for (unsigned i = 0; i < tail.size(); ++i) {
            expr_ref tmp(m);
            var_subst(m, false)(tail[i].get(), var_reprs.size(), (expr*const*)var_reprs.c_ptr(), tmp);
            conj.push_back(tmp);
            TRACE("spacer", tout << mk_pp(tail[i].get(), m) << "\n" << mk_pp(tmp, m) << "\n";);
            SASSERT(is_ground(tmp));
        }         
        expr_ref fml = pm.mk_and(conj);
        th_rewriter rw(m);
        rw(fml);
        if (ctx.get_params ().spacer_blast_term_ite () || ctx.is_dl() || ctx.is_utvpi()) {
          blast_term_ite (fml);
          rw(fml);
         }
        TRACE("spacer", tout << mk_pp(fml, m) << "\n";);
        SASSERT(is_ground(fml));
        if (m.is_false(fml)) {
            // no-op.
        }
        else {
            is_init.push_back (ut_size == 0);
            transitions.push_back(fml);            
            m.inc_ref(fml);
            m_rule2transition.insert(&rule, fml.get());
            rules.push_back(&rule);
        }
        m_rule2inst.insert(&rule,&var_reprs);
        m_rule2vars.insert(&rule, aux_vars);
        TRACE("spacer", 
              tout << rule.get_decl()->get_name() << "\n";
              for (unsigned i = 0; i < var_reprs.size(); ++i) {
                  tout << mk_pp(var_reprs[i].get(), m) << " ";
              }
              tout << "\n";);
    }

    bool pred_transformer::check_filled(app_ref_vector const& v) const {
        for (unsigned i = 0; i < v.size(); ++i) {
            if (!v[i]) return false;
        }
        return true;
    }

    // create constants for free variables in tail.
  void pred_transformer::ground_free_vars(expr* e, app_ref_vector& vars, 
                                          ptr_vector<app>& aux_vars, bool is_init) {
        expr_free_vars fv;
        fv(e);
        while (vars.size() < fv.size()) {
            vars.push_back(0);
        }
        for (unsigned i = 0; i < fv.size(); ++i) {
            if (fv[i] && !vars[i].get()) {
                vars[i] = m.mk_fresh_const("aux", fv[i]);
                vars [i] = m.mk_const (pm.get_n_pred (vars.get (i)->get_decl ()));
                aux_vars.push_back(vars[i].get());
            }
        }
    }

    // create names for variables used in relations.
    void pred_transformer::init_atom(
        decl2rel const& pts, 
        app * atom, 
        app_ref_vector& var_reprs, 
        expr_ref_vector& conj, 
        unsigned tail_idx
        )
    {
        unsigned arity = atom->get_num_args();
        func_decl* head = atom->get_decl();
        pred_transformer& pt = *pts.find(head);
        for (unsigned i = 0; i < arity; i++) {
            app_ref rep(m);
            
            if (tail_idx == UINT_MAX) {
                rep = m.mk_const(pm.o2n(pt.sig(i), 0));
            }
            else {
                rep = m.mk_const(pm.o2o(pt.sig(i), 0, tail_idx));
            }            
                       
            expr * arg = atom->get_arg(i);
            if (is_var(arg)) {
                var * v = to_var(arg);
                unsigned var_idx = v->get_idx();
                if (var_idx >= var_reprs.size()) {
                    var_reprs.resize(var_idx+1);
                }
                expr * repr = var_reprs[var_idx].get();
                if (repr) {
                    conj.push_back(m.mk_eq(rep, repr));
                }
                else {
                    var_reprs[var_idx] = rep;
                }
            }
            else {
                SASSERT(is_app(arg));
                conj.push_back(m.mk_eq(rep, arg));
            }
        }
    }

    void pred_transformer::add_premises(decl2rel const& pts, unsigned lvl, expr_ref_vector& r) {
        r.push_back(pm.get_background());
        r.push_back((lvl == 0)?initial_state():transition());
        for (unsigned i = 0; i < rules().size(); ++i) {
            add_premises(pts, lvl, *rules()[i], r);
        }
    }

    void pred_transformer::close(expr* e) {
        //m_reachable.add_reachable(e);
    }

    void pred_transformer::add_premises(decl2rel const& pts, unsigned lvl, datalog::rule& rule, expr_ref_vector& r) {        
        find_predecessors(rule, m_predicates);
        for (unsigned i = 0; i < m_predicates.size(); ++i) {
            expr_ref tmp(m);
            func_decl* head = m_predicates[i];
            pred_transformer& pt = *pts.find(head);
            expr_ref inv = pt.get_formulas(lvl, false);     
            if (!m.is_true(inv)) {
                pm.formula_n2o(inv, tmp, i, true);
                r.push_back(tmp);
            }
        }
    }

    void pred_transformer::inherit_properties(pred_transformer& other) {
      m_frames.inherit_frames (other.m_frames);
    }

  
  // ------------------
  // legacy_frames
  void pred_transformer::legacy_frames::simplify_formulas (tactic& tac, 
                                                           expr_ref_vector& v) {
    ast_manager &m = m_pt.get_ast_manager ();
    goal_ref g(alloc(goal, m, false, false, false));
    for (unsigned j = 0; j < v.size(); ++j) g->assert_expr(v[j].get()); 
    model_converter_ref mc;
    proof_converter_ref pc;
    expr_dependency_ref core(m);
    goal_ref_buffer result;
    tac(g, result, mc, pc, core);
    SASSERT(result.size() == 1);
    goal* r = result[0];
    v.reset();
    for (unsigned j = 0; j < r->size(); ++j) v.push_back(r->form(j));            
  }
  
  void pred_transformer::legacy_frames::simplify_formulas() {
    ast_manager &m = m_pt.get_ast_manager ();
    tactic_ref us = mk_unit_subsumption_tactic(m);
    simplify_formulas(*us, m_invariants);
    for (unsigned i = 0; i < m_levels.size(); ++i) {
      simplify_formulas(*us, m_levels[i]);
    }             
  }
  
  void pred_transformer::legacy_frames::get_frame_geq_lemmas (unsigned lvl, 
                                                              expr_ref_vector &out)
  {
    get_frame_lemmas (infty_level(), out);
    for (unsigned i = lvl, sz = m_levels.size (); i < sz; ++i)
      get_frame_lemmas (i, out);
  }
  
  bool pred_transformer::legacy_frames::propagate_to_next_level(unsigned src_level) 
  {
      
    ast_manager &m = m_pt.get_ast_manager ();
    if (m_levels.size () <= src_level) return true;
    if (m_levels [src_level].empty ()) return true;
      
    unsigned tgt_level = next_level(src_level);
    m_pt.ensure_level(next_level(tgt_level));
        

    TRACE("spacer", 
           tout << "propagating " << src_level << " to " << tgt_level;
           tout << " for relation " << m_pt.head()->get_name() << "\n";);
                
    for (unsigned i = 0; i < m_levels[src_level].size(); ) {
      expr_ref_vector &src= m_levels[src_level];
      expr * curr = src[i].get();                  
      unsigned stored_lvl;
      VERIFY(m_prop2level.find(curr, stored_lvl));
      SASSERT(stored_lvl >= src_level);
      unsigned solver_level;
      if (stored_lvl > src_level) {
        TRACE("spacer", tout << "at level: "<< stored_lvl << " " << mk_pp(curr, m) << "\n";);
        src[i] = src.back();
        src.pop_back();
      }
      else if (m_pt.is_invariant(tgt_level, curr, solver_level)) {
        // -- might invalidate src reference
        add_lemma (curr, solver_level);
        TRACE("spacer", tout << "is invariant: "<< pp_level(solver_level) << " " << mk_pp(curr, m) << "\n";);              
        // shadow higher-level src
        expr_ref_vector &src = m_levels[src_level];
        src[i] = src.back();
        src.pop_back();
        ++m_pt.m_stats.m_num_propagations;
      }
      else {
        TRACE("spacer", tout << "not propagated: " << mk_pp(curr, m) << "\n";); 
        ++i;
      }
    }        

    CTRACE ("spacer", m_levels[src_level].empty (), 
            tout << "Fully propagated level " 
            << src_level << " of " << m_pt.head ()->get_name () << "\n";);
        
    return m_levels[src_level].empty();
  }
  
  bool pred_transformer::legacy_frames::add_lemma (expr * lemma, unsigned lvl)
  {
    if (is_infty_level (lvl))
    {
      if (!m_invariants.contains (lemma))
      {
        m_invariants.push_back (lemma);
        m_prop2level.insert (lemma, lvl);
        m_pt.add_lemma_core (lemma, lvl);
        return true;
      }
      return false;
    }
    
    unsigned old_level;
    if (!m_prop2level.find (lemma, old_level) || old_level < lvl)
    {
      m_levels[lvl].push_back(lemma);
      m_prop2level.insert(lemma, lvl);
      m_pt.add_lemma_core (lemma, lvl);
      return true;
    }
    return false;
  }
  
  void  pred_transformer::legacy_frames::propagate_to_infinity(unsigned level) 
  {
    TRACE ("spacer", tout << "propagating to oo from lvl " << level 
          << " of " << m_pt.m_head->get_name () << "\n";);
      
    if (m_levels.empty ()) return;
      
    for (unsigned i = m_levels.size (); i > level; --i)
    {
      expr_ref_vector &lemmas = m_levels [i-1];
      for (unsigned j = 0; j < lemmas.size (); ++j)
        add_lemma (lemmas.get (j), infty_level ());
      lemmas.reset();
    }
  }
  
  void pred_transformer::legacy_frames::inherit_frames (legacy_frames& other)
  {
    
    SASSERT(m_pt.m_head == other.m_pt.m_head);
    obj_map<expr, unsigned>::iterator it  = other.m_prop2level.begin();
    obj_map<expr, unsigned>::iterator end = other.m_prop2level.end();        
    for (; it != end; ++it) add_lemma (it->m_key, it->m_value);
  }
  
  bool pred_transformer::frames::add_lemma (expr * lemma, unsigned level)
  {
    TRACE ("spacer", tout << "add-lemma: " << pp_level (level) << " " 
           << m_pt.head ()->get_name () << " " 
           << mk_pp (lemma, m_pt.get_ast_manager ()) << "\n";);
    
    for (unsigned i = 0, sz = m_lemmas.size (); i < sz; ++i)
      if (m_lemmas [i].get () == lemma)
      {
        if (m_lemmas [i].level () >= level) 
        {
          TRACE ("spacer", tout << "Already at a higher level: " 
                 << pp_level (m_lemmas [i].level ()) << "\n";);
          
          return false;
        }
        
        m_lemmas [i].set_level (level);
        m_pt.add_lemma_core (lemma, level);
        for (unsigned j = i; (j+1) < sz && m_lt (m_lemmas [j+1], m_lemmas[j]); ++j)
          swap (m_lemmas [j], m_lemmas [j+1]);
        return true;
      }
    
    frames::lemma lem (m_pt.get_ast_manager (), lemma, level);
    m_lemmas.push_back (lem);
    m_sorted = false;
    m_pt.add_lemma_core (m_lemmas.back ().get (), m_lemmas.back ().level ());
    return true;
  }
  
  void pred_transformer::frames::propagate_to_infinity (unsigned level)
  {
    for (unsigned i = 0, sz = m_lemmas.size (); i < sz; ++i)
      if (m_lemmas[i].level () >= level && !is_infty_level (m_lemmas [i].level ())) 
      {
        m_lemmas [i].set_level (infty_level ());
        m_pt.add_lemma_core (m_lemmas [i].get (), infty_level ());
        m_sorted = false;
      }
  }
  
  void pred_transformer::frames::sort ()
  {
    if (m_sorted) return;
    
    m_sorted = true;
    std::sort (m_lemmas.begin (), m_lemmas.end (), m_lt);
  }
  
  bool pred_transformer::frames::propagate_to_next_level (unsigned level)
  {
    sort ();
    bool all = true;
    
    
    if (m_lemmas.empty ()) return all;
    
    unsigned tgt_level = next_level (level);
    m_pt.ensure_level (tgt_level);
    
    for (unsigned i = 0, sz = m_lemmas.size (); i < sz && m_lemmas [i].level () <= level;)
    {
      if (m_lemmas [i].level () < level) 
      {++i; continue;}
      
      
      unsigned solver_level;
      expr * curr = m_lemmas [i].get ();
      if (m_pt.is_invariant (tgt_level, curr, solver_level))
      {
        m_lemmas [i].set_level (solver_level);
        m_pt.add_lemma_core (m_lemmas [i].get (), solver_level);
        
        // percolate the lemma up to its new place
        for (unsigned j = i; (j+1) < sz && m_lt (m_lemmas[j+1], m_lemmas[j]); ++j)
          swap (m_lemmas [j], m_lemmas[j+1]);
        
      }
      else 
      {
        all = false;
        ++i;
      }
    }
    
    return all;
  }

  void pred_transformer::frames::simplify_formulas ()
  {
    ast_manager &m = m_pt.get_ast_manager ();
    sort ();
    
    tactic_ref simplifier = mk_unit_subsumption_tactic (m);
    vector<lemma> old_lemmas (m_lemmas);
    unsigned lemmas_size = old_lemmas.size ();
    m_lemmas.reset ();
    
    goal_ref g (alloc (goal, m, false, false, false));
    
    unsigned j = 0;
    for (unsigned i = 0; i <= m_size; ++i)
    {
      g->reset_all ();
      unsigned level = i < m_size ? i : infty_level ();
      
      model_converter_ref mc;
      proof_converter_ref pc;
      expr_dependency_ref core(m);
      goal_ref_buffer result;
      
      for (; j < lemmas_size && old_lemmas [j].level () <= level; ++j)
        if (old_lemmas [j].level () == level) g->assert_expr (old_lemmas [j].get ());
      
      if (g->size () <= 0) continue;
      
      (*simplifier) (g, result, mc, pc, core);
      SASSERT (result.size () == 1);
      goal *r = result [0];
      
      for (unsigned k = 0; k < r->size (); ++k) 
        m_lemmas.push_back (lemma (m, r->form (k), level));
      m_sorted = false;
    }
  }


  app* pred_transformer::extend_initial (expr *e)
  {
    // create fresh extend literal
    app_ref v(m);
    v = m.mk_fresh_const (m_head->get_name ().str ().c_str (),
                          m.mk_bool_sort ());
    v = m.mk_const (pm.get_n_pred (v->get_decl ()));
    
    // -- extend the initial condition
    m_solver.add_formula (m.mk_or (m_extend_lit, e, v));

    // -- remember the new extend literal
    m_extend_lit = m.mk_not (v);

    return m_extend_lit;
  }
  
  
    // ----------------
    // derivation

  derivation::derivation (model_node& parent, datalog::rule const& rule,
                          expr * trans) :
        m_parent (parent),
        m_rule (rule),
        m_premises (),
        m_active (0),
        m_trans (trans, m_parent.get_ast_manager ()) {} 
  
  derivation::premise::premise (pred_transformer &pt, unsigned oidx, 
                                expr *summary, bool must,
                                const ptr_vector<app> *aux_vars) : 
    m_pt (pt), m_oidx (oidx), 
    m_summary (summary, pt.get_ast_manager ()), m_must (must),
    m_ovars (pt.get_ast_manager ())
  {
    
    ast_manager &m = m_pt.get_ast_manager ();
    manager &sm = m_pt.get_manager ();
    
    unsigned sig_sz = m_pt.head ()->get_arity ();
    for (unsigned i = 0; i < sig_sz; ++i)
      m_ovars.push_back (m.mk_const (sm.o2o (pt.sig (i), 0, m_oidx)));
    
    if (aux_vars)
      for (unsigned i = 0, sz = aux_vars->size (); i < sz; ++i)
        m_ovars.push_back (m.mk_const (sm.n2o (aux_vars->get (i)->get_decl (), m_oidx)));
  }
  
  derivation::premise::premise (const derivation::premise &p) :
    m_pt (p.m_pt), m_oidx (p.m_oidx), m_summary (p.m_summary), m_must (p.m_must),
    m_ovars (p.m_ovars) {}
  
  /// \brief Updated the summary. 
  /// The new summary is over n-variables. 
  void derivation::premise::set_summary (expr * summary, bool must, 
                                         const ptr_vector<app> *aux_vars)
  {
    ast_manager &m = m_pt.get_ast_manager ();
    manager &sm = m_pt.get_manager ();
    unsigned sig_sz = m_pt.head ()->get_arity ();
    
    m_must = must;
    sm.formula_n2o (summary, m_summary, m_oidx);
    
    m_ovars.reset ();
    for (unsigned i = 0; i < sig_sz; ++i)
      m_ovars.push_back (m.mk_const (sm.o2o (m_pt.sig (i), 0, m_oidx)));
    
    if (aux_vars)
      for (unsigned i = 0, sz = aux_vars->size (); i < sz; ++i)
        m_ovars.push_back (m.mk_const (sm.n2o (aux_vars->get (i)->get_decl (), 
                                               m_oidx)));
  }
  
  
  void derivation::add_premise (pred_transformer &pt, 
                                unsigned oidx,
                                expr* summary,
                                bool must,
                                const ptr_vector<app> *aux_vars)
  {m_premises.push_back (premise (pt, oidx, summary, must, aux_vars));}
  


  model_node *derivation::create_first_child (model_evaluator &mev)
  {
    if (m_premises.empty ()) return NULL;
    m_active = 0;
    return create_next_child (mev);
  }
  
  model_node *derivation::create_next_child (model_evaluator &mev)
  {
    timeit _timer (is_trace_enabled("spacer_timeit"), 
                   "spacer::derivation::create_next_child", 
                   verbose_stream ());

    ast_manager &m = get_ast_manager ();
    expr_ref_vector summaries (m);
    app_ref_vector vars (m);
    
    // -- find first may premise
    while (m_active < m_premises.size () && m_premises[m_active].is_must ())
    {
      summaries.push_back (m_premises[m_active].get_summary ());
      vars.append (m_premises[m_active].get_ovars ());
      ++m_active;
    }
    if (m_active >= m_premises.size ()) return NULL;
    
    // -- update m_trans with the pre-image of m_trans over the must summaries
    summaries.push_back (m_trans);
    m_trans = get_manager ().mk_and (summaries);
    summaries.reset ();
    
    if (!vars.empty ()) 
    {
      timeit _timer1 (is_trace_enabled("spacer_timeit"), 
                      "create_next_child::qproject1", 
                      verbose_stream ());
      qe_project (m, vars, m_trans, mev.get_model (), true);
      //qe::reduce_array_selects (*mev.get_model (), m_trans);
    }
    
        
    
    
    // create the post condition by compute post-image over summaries
    // that precede currently active premise
    vars.reset ();
    for (unsigned i = m_active + 1; i < m_premises.size (); ++i)
    {
      summaries.push_back (m_premises [i].get_summary ());
      vars.append (m_premises [i].get_ovars ());
    }
    summaries.push_back (m_trans);
    
    expr_ref post(m);
    post = get_manager ().mk_and (summaries);
    summaries.reset ();
    if (!vars.empty ()) 
    {
      timeit _timer2 (is_trace_enabled("spacer_timeit"),
                      "create_next_child::qproject2", 
                      verbose_stream ());
      qe_project (m, vars, post, mev.get_model (), true);
      //qe::reduce_array_selects (*mev.get_model (), post);
    }
    
    get_manager ().formula_o2n (post.get (), post, m_premises [m_active].get_oidx ());
    
    model_node *n = alloc (model_node, &m_parent, 
                           m_premises[m_active].pt (), 
                           prev_level (m_parent.level ()),
                           m_parent.depth ());
    n->set_post (post);
    return n;
  }
  
  model_node *derivation::create_next_child ()
  {
    if (m_active + 1 >= m_premises.size ()) return NULL;
    
    // update the summary of the active node to some must summary
    
    // construct a new model consistent with the must summary of m_active premise
    pred_transformer &pt = m_premises[m_active].pt ();
    model_ref model;
    
    ast_manager &m = get_ast_manager ();
    manager &pm = get_manager ();
    
    expr_ref_vector summaries (m);
    
    for (unsigned i = m_active + 1; i < m_premises.size (); ++i)
      summaries.push_back (m_premises [i].get_summary ());
    
    // -- orient transition relation towards m_active premise
    expr_ref active_trans (m);
    pm.formula_o2n (m_trans, active_trans, 
                    m_premises[m_active].get_oidx (), false);
    summaries.push_back (active_trans);
    
    // if not true, bail out, the must summary of m_active is not strong enough
    // this is possible if m_post was weakened for some reason
    if (!pt.is_must_reachable (pm.mk_and (summaries), &model)) return NULL;
    
    model_evaluator mev (m, model);
    
    // find must summary used
    
    reach_fact *rf = pt.get_used_reach_fact (mev, true);
    
    // get an implicant of the summary
    expr_ref_vector u(m), lits (m);
    u.push_back (rf->get ());
    compute_implicant_literals (mev, u, lits);
    expr_ref v(m);
    v = pm.mk_and (lits);
    
    // XXX The summary is not used by anyone after this point
    m_premises[m_active].set_summary (v, true, &(rf->aux_vars ()));

    
    /** HACK: needs a rewrite 
     * compute post over the new must summary this must be done here
     * because the must summary is currently described over new
     * variables. However, we store it over old-variables, but we do
     * not update the model. So we must get rid of all of the
     * new-variables at this point.
     */
    {
      pred_transformer &pt = m_premises[m_active].pt ();
      app_ref_vector vars (m);
      
      summaries.reset ();
      summaries.push_back (v);
      summaries.push_back (active_trans);
      m_trans = pm.mk_and (summaries);
      
      // variables to eliminate
      vars.append (rf->aux_vars ().size (), rf->aux_vars ().c_ptr ());
      for (unsigned i = 0, sz = pt.head ()->get_arity (); i < sz; ++i)
        vars.push_back (m.mk_const (pm.o2n (pt.sig (i), 0)));
      
      if (!vars.empty ()) qe_project (m, vars, m_trans, mev.get_model (), true);
    }
    
    
    
    m_active++;
    
    return create_next_child (mev);
  }
  
    // ----------------
    // model_search

  model_node* model_search::top ()
  {
    /// nothing in the queue
    if (m_obligations.empty ()) return NULL;
    /// top queue element is above max level
    if (m_obligations.top ()->level () > m_max_level) return NULL;
    /// top queue element is at the max level, but at a higher than base depth
    if (m_obligations.top ()->level () == m_max_level && 
        m_obligations.top ()->depth () > m_min_depth) return NULL;
    
    /// there is something good in the queue
    return m_obligations.top ().get ();
  }
  
    void model_search::set_root (model_node& root) {
        m_root = &root;
        m_max_level = root.level ();
        m_min_depth = root.depth ();
        reset();
    }

    /**
       Extract trace comprising of constraints 
       and predicates that are satisfied from facts to the query.
       The resulting trace 
     */
    expr_ref model_search::get_trace(context const& ctx) {
        ast_manager& m = ctx.get_ast_manager ();
        return expr_ref (m.mk_true (), m);
    }
  
    model_search::~model_search() {}

    void model_search::reset() {
        while (!m_obligations.empty ()) m_obligations.pop ();
        if (m_root) m_obligations.push (m_root);
    }
  
    // ----------------
    // context

    context::context(
        smt_params&     fparams,
        fixedpoint_params const&     params,
        ast_manager&          m
        )
        : m_fparams(fparams),
          m_params(params),
          m(m),
          m_context(0),
          m_pm(m_fparams, params.pdr_max_num_contexts(), m),
          m_query_pred(m),
          m_query(0),
          m_search(),
          m_last_result(l_undef),
          m_inductive_lvl(0),
          m_expanded_lvl(0),
          m_cancel(false)
    {
    }

    context::~context() {
        reset_core_generalizers();
        reset();
    }

    void context::reset() {
        TRACE("spacer", tout << "\n";);
        cleanup();
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        m_rels.reset();
        m_search.reset();
        m_query = 0;       
        m_last_result = l_undef;
        m_inductive_lvl = 0;        
    }

    void context::init_rules(datalog::rule_set& rules, decl2rel& rels) {
        m_context = &rules.get_context();
        // Allocate collection of predicate transformers
        datalog::rule_set::decl2rules::iterator dit = rules.begin_grouped_rules(), dend = rules.end_grouped_rules();
        decl2rel::obj_map_entry* e;
        for (; dit != dend; ++dit) {            
            func_decl* pred = dit->m_key;
            TRACE("spacer", tout << mk_pp(pred, m) << "\n";);
            SASSERT(!rels.contains(pred));
            e = rels.insert_if_not_there2(pred, alloc(pred_transformer, *this, 
                                                      get_manager(), pred));            
            datalog::rule_vector const& pred_rules = *dit->m_value;            
            for (unsigned i = 0; i < pred_rules.size(); ++i) {
                e->get_data().m_value->add_rule(pred_rules[i]);
            }
        }
        datalog::rule_set::iterator rit = rules.begin(), rend = rules.end();
        for (; rit != rend; ++rit) {
            datalog::rule* r = *rit;
            pred_transformer* pt;
            unsigned utz = r->get_uninterpreted_tail_size();
            for (unsigned i = 0; i < utz; ++i) {
                func_decl* pred = r->get_decl(i);
                if (!rels.find(pred, pt)) {
                    pt = alloc(pred_transformer, *this, get_manager(), pred);
                    rels.insert(pred, pt);                
                }
            }
        }
        // Initialize use list dependencies
        decl2rel::iterator it = rels.begin(), end = rels.end();        
        for (; it != end; ++it) {
            func_decl* pred = it->m_key;      
            pred_transformer* pt = it->m_value, *pt_user;
            obj_hashtable<func_decl> const& deps = rules.get_dependencies().get_deps(pred);
            obj_hashtable<func_decl>::iterator itf = deps.begin(), endf = deps.end();
            for (; itf != endf; ++itf) {
                TRACE("spacer", tout << mk_pp(pred, m) << " " << mk_pp(*itf, m) << "\n";);
                pt_user = rels.find(*itf);
                pt_user->add_use(pt);                
            }
        }      

        // Initialize the predicate transformers.
        it = rels.begin(), end = rels.end();        
        for (; it != end; ++it) {            
            pred_transformer& rel = *it->m_value;
            rel.initialize(rels);
            TRACE("spacer", rel.display(tout); );
        }
        
        // initialize reach facts
        it = rels.begin (), end = rels.end ();
        for (; it != end; ++it)
          it->m_value->init_reach_facts ();        
    }

    void context::update_rules(datalog::rule_set& rules) {
        decl2rel rels;
        init_core_generalizers(rules);
        init_rules(rules, rels); 
        decl2rel::iterator it = rels.begin(), end = rels.end();
        for (; it != end; ++it) {
            pred_transformer* pt = 0;
            if (m_rels.find(it->m_key, pt)) {
                it->m_value->inherit_properties(*pt);
            }
        }
        reset();
        it = rels.begin(), end = rels.end();
        for (; it != end; ++it) {
            m_rels.insert(it->m_key, it->m_value);
        }
    }

    unsigned context::get_num_levels(func_decl* p) {
        pred_transformer* pt = 0;
        if (m_rels.find(p, pt)) {
            return pt->get_num_levels();
        }
        else {
            IF_VERBOSE(10, verbose_stream() << "did not find predicate " << p->get_name() << "\n";);
            return 0;
        }
    }

    expr_ref context::get_cover_delta(int level, func_decl* p_orig, func_decl* p) {
        pred_transformer* pt = 0;
        if (m_rels.find(p, pt)) {
            return pt->get_cover_delta(p_orig, level);
        }
        else {
            IF_VERBOSE(10, verbose_stream() << "did not find predicate " << p->get_name() << "\n";);
            return expr_ref(m.mk_true(), m);
        }
    }

    void context::add_cover(int level, func_decl* p, expr* property) {
        pred_transformer* pt = 0;
        if (!m_rels.find(p, pt)) {
            pt = alloc(pred_transformer, *this, get_manager(), p);
            m_rels.insert(p, pt);
            IF_VERBOSE(10, verbose_stream() << "did not find predicate " << p->get_name() << "\n";);
        }
        unsigned lvl = (level == -1)?infty_level():((unsigned)level);
        pt->add_cover(lvl, property);
    }

    class context::classifier_proc {
        ast_manager& m;
        arith_util a;
        bool m_is_bool;
        bool m_is_bool_arith;
        bool m_has_arith;
        bool m_is_dl;
        bool m_is_utvpi;
    public:
        classifier_proc(ast_manager& m, datalog::rule_set& rules):
            m(m), a(m), m_is_bool(true), m_is_bool_arith(true), m_has_arith(false), m_is_dl(false), m_is_utvpi(false) {
            classify(rules);
        }
        void operator()(expr* e) {
            if (m_is_bool) {                
                if (!m.is_bool(e)) {
                    m_is_bool = false;
                }
                else if (is_var(e)) {
                    // no-op.
                }
                else if (!is_app(e)) {
                    m_is_bool = false;
                }
                else if (to_app(e)->get_num_args() > 0 &&
                         to_app(e)->get_family_id() != m.get_basic_family_id()) {
                    m_is_bool = false;
                }
            }

            m_has_arith = m_has_arith || a.is_int_real(e);

            if (m_is_bool_arith) {                
                if (!m.is_bool(e) && !a.is_int_real(e)) {
                    m_is_bool_arith = false;
                }
                else if (is_var(e)) {
                    // no-op
                }
                else if (!is_app(e)) {
                    m_is_bool_arith = false;
                }
                else if (to_app(e)->get_num_args() > 0 &&
                         to_app(e)->get_family_id() != m.get_basic_family_id() &&
                         to_app(e)->get_family_id() != a.get_family_id()) {
                    m_is_bool_arith = false;
                }
            }
        }

        bool is_bool() const { return m_is_bool; }

        bool is_bool_arith() const { return m_is_bool_arith; }

        bool is_dl() const { return m_is_dl; }

        bool is_utvpi() const { return m_is_utvpi; }

    private:

        void classify(datalog::rule_set& rules) {
            expr_fast_mark1 mark;
            datalog::rule_set::iterator it = rules.begin(), end = rules.end();        
            for (; it != end; ++it) {      
                datalog::rule& r = *(*it);
                classify_pred(mark, r.get_head());
                unsigned utsz = r.get_uninterpreted_tail_size();
                for (unsigned i = 0; i < utsz; ++i) {
                    classify_pred(mark, r.get_tail(i));                
                }
                for (unsigned i = utsz; i < r.get_tail_size(); ++i) {
                    quick_for_each_expr(*this, mark, r.get_tail(i));                    
                }
            }
            mark.reset();
 
            m_is_dl = false;
            m_is_utvpi = false;
            if (m_has_arith) {
                ptr_vector<expr> forms;
                for (it = rules.begin(); it != end; ++it) {  
                    datalog::rule& r = *(*it);
                    unsigned utsz = r.get_uninterpreted_tail_size();
                    forms.push_back(r.get_head());
                    for (unsigned i = utsz; i < r.get_tail_size(); ++i) {
                        forms.push_back(r.get_tail(i));
                    }         
                }
                m_is_dl = is_difference_logic(m, forms.size(), forms.c_ptr());
                m_is_utvpi = m_is_dl || is_utvpi_logic(m, forms.size(), forms.c_ptr());
            }
        }

        void classify_pred(expr_fast_mark1& mark, app* pred) {
            for (unsigned i = 0; i < pred->get_num_args(); ++i) {
                quick_for_each_expr(*this, mark, pred->get_arg(i));
            }
        }
    };

    bool context::validate() {
        if (!m_params.pdr_validate_result()) return true;
        
        std::stringstream msg;

        switch(m_last_result) {
        case l_true: {
            TRACE ("spacer", tout << "Unsupported\n";);
            break;
            /*scoped_no_proof _sc(m);
            expr_ref const& cex = get_answer ();
            smt::kernel solver (m, get_fparams());
            solver.assert_expr (cex);
            lbool res = solver.check ();
            if (res == l_true) {
                TRACE ("spacer", tout << "Validation Succeeded\n";);
            } else {
                msg << "proof validation failed";
                IF_VERBOSE(0, verbose_stream() << msg.str() << "\n";);
                throw default_exception(msg.str());
            }*/
            /*proof_ref pr = get_proof();
            proof_checker checker(m);
            expr_ref_vector side_conditions(m);
            bool ok = checker.check(pr, side_conditions);
            if (!ok) {
                msg << "proof validation failed";
                IF_VERBOSE(0, verbose_stream() << msg.str() << "\n";);
                throw default_exception(msg.str());
            }
            for (unsigned i = 0; i < side_conditions.size(); ++i) {
                expr* cond = side_conditions[i].get();
                expr_ref tmp(m);
                tmp = m.mk_not(cond);
                IF_VERBOSE(2, verbose_stream() << "checking side-condition:\n" << mk_pp(cond, m) << "\n";);
                smt::kernel solver(m, get_fparams());
                solver.assert_expr(tmp);
                lbool res = solver.check();
                if (res != l_false) {
                    msg << "rule validation failed when checking: " << mk_pp(cond, m);
                    IF_VERBOSE(0, verbose_stream() << msg.str() << "\n";);
                    throw default_exception(msg.str());
                }                                
            }*/
            break;
        }            
        case l_false: {
            expr_ref_vector refs(m);
            expr_ref tmp(m);
            model_ref model;
            vector<relation_info> rs;
            model_converter_ref mc;
            get_level_property(m_inductive_lvl, refs, rs);    
            inductive_property ex(m, mc, rs);
            ex.to_model(model);
            decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
            var_subst vs(m, false);   
            for (; it != end; ++it) {
                ptr_vector<datalog::rule> const& rules = it->m_value->rules();
                TRACE ("spacer", tout << "PT: " << it->m_value->head ()->get_name ().str ()
                                      << "\n";);
                for (unsigned i = 0; i < rules.size(); ++i) {
                    datalog::rule& r = *rules[i];
                    
                    TRACE ("spacer", 
                           get_datalog_context ().
                           get_rule_manager ().
                           display_smt2(r, tout) << "\n";);
                    
                    model->eval(r.get_head(), tmp);
                    expr_ref_vector fmls(m);
                    fmls.push_back(m.mk_not(tmp));
                    unsigned utsz = r.get_uninterpreted_tail_size();
                    unsigned tsz  = r.get_tail_size();
                    for (unsigned j = 0; j < utsz; ++j) {
                        model->eval(r.get_tail(j), tmp);
                        fmls.push_back(tmp);
                    }
                    for (unsigned j = utsz; j < tsz; ++j) {
                        fmls.push_back(r.get_tail(j));
                    }
                    tmp = m.mk_and(fmls.size(), fmls.c_ptr()); 
                    svector<symbol> names;
                    expr_free_vars fv;
                    fv (tmp);
                    fv.set_default_sort (m.mk_bool_sort ());
                    
                    for (unsigned i = 0; i < fv.size(); ++i) {
                      names.push_back(symbol(fv.size () - i - 1));
                    }
                    if (!fv.empty()) {
                        fv.reverse ();
                        tmp = m.mk_exists(fv.size(), fv.c_ptr(), names.c_ptr(), tmp);
                    }
                    smt::kernel solver(m, get_fparams());
                    solver.assert_expr(tmp);
                    lbool res = solver.check();
                    if (res != l_false) {
                        msg << "rule validation failed when checking: " 
                            << mk_pp(tmp, m);
                        IF_VERBOSE(0, verbose_stream() << msg.str() << "\n";);
                        throw default_exception(msg.str());
                        return false;
                    }
                }
            }
            TRACE ("spacer", tout << "Validation Succeeded\n";);
            break;
        }
        default:
            break;
        }
        return true;
    }


    void context::reset_core_generalizers() {
        std::for_each(m_core_generalizers.begin(), m_core_generalizers.end(), delete_proc<core_generalizer>());
        m_core_generalizers.reset();
    }

    void context::init_core_generalizers(datalog::rule_set& rules) {
        reset_core_generalizers();
        classifier_proc classify(m, rules);
        bool use_mc = m_params.pdr_use_multicore_generalizer();
        if (use_mc) {
            m_core_generalizers.push_back(alloc(core_multi_generalizer, *this, 0));
        }
        if (m_params.pdr_farkas() && !classify.is_bool()) {
            m.toggle_proof_mode(PGM_FINE);
            m_fparams.m_arith_bound_prop = BP_NONE;
            m_fparams.m_arith_auto_config_simplex = true;
            m_fparams.m_arith_propagate_eqs = false;
            m_fparams.m_arith_eager_eq_axioms = false;
            if (m_params.pdr_utvpi()) {
                if (classify.is_dl()) {
                    m_fparams.m_arith_mode = AS_DIFF_LOGIC;
                    m_fparams.m_arith_expand_eqs = true;
                } else if (classify.is_utvpi()) {
                    IF_VERBOSE(1, verbose_stream() << "UTVPI\n";);
                    m_fparams.m_arith_mode = AS_UTVPI;
                    m_fparams.m_arith_expand_eqs = true;                
                }
            }
        }
        if (!use_mc && m_params.pdr_use_inductive_generalizer()) {
            m_core_generalizers.push_back(alloc(core_bool_inductive_generalizer, *this, 0));
        }
        if (m_params.pdr_inductive_reachability_check()) {
            m_core_generalizers.push_back(alloc(core_induction_generalizer, *this));
        }
        if (m_params.pdr_use_arith_inductive_generalizer()) {
            m_core_generalizers.push_back(alloc(core_arith_inductive_generalizer, *this));
        }
        
        if (m_params.use_array_eq_generalizer ()) 
          m_core_generalizers.push_back (alloc (core_array_eq_generalizer, *this));
        
    }

    void context::get_level_property(unsigned lvl, expr_ref_vector& res, vector<relation_info>& rs) const {
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (; it != end; ++it) {
            pred_transformer* r = it->m_value;
            if (r->head() == m_query_pred) {
                continue;
            }
            expr_ref conj = r->get_formulas(lvl, false);        
            m_pm.formula_n2o(0, false, conj);            
            res.push_back(conj);
            ptr_vector<func_decl> sig(r->head()->get_arity(), r->sig());
            rs.push_back(relation_info(m, r->head(), sig, conj));
        }
    }

    void context::simplify_formulas() {
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (; it != end; ++it) {
            pred_transformer* r = it->m_value;
            r->simplify_formulas();
        }        
    }

  lbool context::solve(unsigned from_lvl) {
    m_last_result = l_undef;
    try {
      m_last_result = solve_core (from_lvl);
      if (m_last_result == l_false)
      {
        simplify_formulas();
        m_last_result = l_false;
        //TRACE("spacer",  display_certificate(tout););      
        IF_VERBOSE(1, {
            expr_ref_vector refs(m);
            vector<relation_info> rs;
            get_level_property(m_inductive_lvl, refs, rs);    
            model_converter_ref mc;
            inductive_property ex(m, mc, rs);
            verbose_stream() << ex.to_string();
          });
            
        // upgrade invariants that are known to be inductive.
        // decl2rel::iterator it = m_rels.begin (), end = m_rels.end ();
        // for (; m_inductive_lvl > 0 && it != end; ++it) {
        //   if (it->m_value->head() != m_query_pred) {
        //     it->m_value->propagate_to_infinity (m_inductive_lvl);	
        //   }
        // }
      }            
      VERIFY (validate ());
    }
    catch (unknown_exception) 
    {}

    if (m_last_result == l_true) {
        m_stats.m_cex_depth = get_cex_depth ();
    }
        
    if (m_params.print_statistics ()) {
      statistics st;
      collect_statistics (st);
      st.display_smt2 (verbose_stream ());
    }

    return m_last_result;
  }


    void context::cancel() {
        m_cancel = true;
    }

    void context::cleanup() {
        m_cancel = false;
    }

    void context::checkpoint() {
        if (m_cancel) {
            throw default_exception("spacer canceled");
        }
    }

    unsigned context::get_cex_depth () {
        if (m_last_result != l_true) {
          IF_VERBOSE(1, 
                     verbose_stream () 
                     << "Trace unavailable when result is false\n";);
            return 0;
        }

        // treat the following as queues: read from left to right and insert at right
        ptr_vector<func_decl> preds;
        ptr_vector<pred_transformer> pts;
        reach_fact_ref_vector facts;

        // temporary
        reach_fact* fact;
        datalog::rule const* r;
        pred_transformer* pt;

        // get and discard query rule
        fact = m_query->get_last_reach_fact ();
        r = &fact->get_rule ();

        unsigned cex_depth = 0;

        // initialize queues
        // assume that the query is only on a single predicate
        // (i.e. disallow fancy queries for now)
        facts.append (fact->get_justifications ());
        if (facts.size () != 1) 
        {
          // XXX AG: Escape if an assertion is about to fail
          IF_VERBOSE(1, 
                     verbose_stream () << 
                     "Warning: counterexample is trivial or non-existent\n";);
          return cex_depth;
        }
        SASSERT (facts.size () == 1);
        m_query->find_predecessors (*r, preds);
        SASSERT (preds.size () == 1);
        pts.push_back (&(get_pred_transformer (preds[0])));

        pts.push_back (NULL); // cex depth marker

        // bfs traversal of the query derivation tree
        for (unsigned curr = 0; curr < pts.size (); curr++) {
            // get current pt and fact
            pt = pts.get (curr);
            // check for depth marker
            if (pt == NULL) {
                ++cex_depth;
                // insert new marker if there are pts at higher depth
                if (curr + 1 < pts.size ()) pts.push_back (NULL);
                continue;
            }
            fact = facts.get (curr - cex_depth); // discount the number of markers
            // get rule justifying the derivation of fact at pt
            r = &fact->get_rule ();
            TRACE ("spacer",
                    tout << "next rule: " << r->name ().str () << "\n";
                  );
            // add child facts and pts
            facts.append (fact->get_justifications ());
            pt->find_predecessors (*r, preds);
            for (unsigned j = 0; j < preds.size (); j++) {
                pts.push_back (&(get_pred_transformer (preds[j])));
            }
        }

        return cex_depth;
    }

    /**
       \brief retrieve answer.
    */

    void context::get_rules_along_trace (datalog::rule_ref_vector& rules) {
        if (m_last_result != l_true) {
          IF_VERBOSE(1, 
                     verbose_stream () 
                     << "Trace unavailable when result is false\n";);
            return;
        }

        // treat the following as queues: read from left to right and insert at right
        ptr_vector<func_decl> preds;
        ptr_vector<pred_transformer> pts;
        reach_fact_ref_vector facts;

        // temporary
        reach_fact* fact;
        datalog::rule const* r;
        pred_transformer* pt;

        // get query rule
        fact = m_query->get_last_reach_fact ();
        r = &fact->get_rule ();
        rules.push_back (const_cast<datalog::rule *> (r));
        TRACE ("spacer",
                tout << "Initial rule: " << r->name().str() << "\n";
               );

        // initialize queues
        // assume that the query is only on a single predicate
        // (i.e. disallow fancy queries for now)
        facts.append (fact->get_justifications ());
        if (facts.size () != 1) 
        {
          // XXX AG: Escape if an assertion is about to fail
          IF_VERBOSE(1, 
                     verbose_stream () << 
                     "Warning: counterexample is trivial or non-existent\n";);
          return;
        }
        SASSERT (facts.size () == 1);
        m_query->find_predecessors (*r, preds);
        SASSERT (preds.size () == 1);
        pts.push_back (&(get_pred_transformer (preds[0])));

        // populate rules according to a preorder traversal of the query derivation tree
        for (unsigned curr = 0; curr < pts.size (); curr++) {
            // get current pt and fact
            pt = pts.get (curr);
            fact = facts.get (curr);
            // get rule justifying the derivation of fact at pt
            r = &fact->get_rule ();
            rules.push_back (const_cast<datalog::rule *> (r));
            TRACE ("spacer",
                    tout << "next rule: " << r->name ().str () << "\n";
                  );
            // add child facts and pts
            facts.append (fact->get_justifications ());
            pt->find_predecessors (*r, preds);
            for (unsigned j = 0; j < preds.size (); j++) {
                pts.push_back (&(get_pred_transformer (preds[j])));
            }
        }
    }

    model_ref context::get_model () {
        return model_ref ();
    }
    proof_ref context::get_proof () const {
        return proof_ref (m);
    }

    expr_ref context::get_answer() {
        switch(m_last_result) {
        case l_true: return mk_sat_answer();
        case l_false: return mk_unsat_answer();
        default: return expr_ref(m.mk_true(), m);
        }
    }


    /**
        \brief Retrieve satisfying assignment with explanation.
    */
    expr_ref context::mk_sat_answer() const {
        if (m_params.generate_proof_trace()) {
            IF_VERBOSE(0, verbose_stream() << "Unsupported" << "\n";);
            return expr_ref(m.mk_true(), m);
            //proof_ref pr = get_proof();
            //return expr_ref(pr.get(), m);
        }
        return m_search.get_trace(*this);
    }


    expr_ref context::mk_unsat_answer() const {
        expr_ref_vector refs(m);
        vector<relation_info> rs;
        get_level_property(m_inductive_lvl, refs, rs);            
        inductive_property ex(m, const_cast<model_converter_ref&>(m_mc), rs);
        return ex.to_expr();
    }

    expr_ref context::get_ground_sat_answer () {
        if (m_last_result != l_true) {
            verbose_stream () << "Sat answer unavailable when result is false\n";
            return expr_ref (m);
        }

        // treat the following as queues: read from left to right and insert at the right
        reach_fact_ref_vector reach_facts;
        ptr_vector<func_decl> preds;
        ptr_vector<pred_transformer> pts;
        expr_ref_vector cex (m), // pre-order list of ground instances of predicates
                        cex_facts (m); // equalities for the ground cex using signature constants

        // temporary
        reach_fact *reach_fact;
        pred_transformer* pt;
        expr_ref cex_fact (m);
        datalog::rule const* r;

        // get and discard query rule
        reach_fact = m_query->get_last_reach_fact ();
        r = &reach_fact->get_rule ();

        // initialize queues
        reach_facts.append (reach_fact->get_justifications ());
        SASSERT (reach_facts.size () == 1);
        m_query->find_predecessors (*r, preds);
        SASSERT (preds.size () == 1);
        pts.push_back (&(get_pred_transformer (preds[0])));
        cex_facts.push_back (m.mk_true ());
        
        // XXX a hack to avoid assertion when query predicate is not nullary
        if (preds[0]->get_arity () == 0)
          cex.push_back (m.mk_const (preds[0]));

        // smt context to obtain local cexes
        scoped_ptr<smt::kernel> cex_ctx = alloc (smt::kernel, m, get_fparams ());
        model_evaluator mev (m);

        // preorder traversal of the query derivation tree
        for (unsigned curr = 0; curr < pts.size (); curr++) {
            // pick next pt, fact, and cex_fact
            pt = pts.get (curr);
            reach_fact = reach_facts[curr];
            
            cex_fact = cex_facts.get (curr);

            ptr_vector<pred_transformer> child_pts;

            // get justifying rule and child facts for the derivation of reach_fact at pt
            r = &reach_fact->get_rule ();
            const reach_fact_ref_vector &child_reach_facts = 
              reach_fact->get_justifications ();
            // get child pts
            preds.reset (); pt->find_predecessors (*r, preds);
            for (unsigned j = 0; j < preds.size (); j++) {
                child_pts.push_back (&(get_pred_transformer (preds[j])));
            }
            // update the queues
            reach_facts.append (child_reach_facts);
            pts.append (child_pts);

            // update cex and cex_facts by making a local sat check:
            // check consistency of reach facts of children, rule body, and cex_fact
            cex_ctx->push ();
            cex_ctx->assert_expr (cex_fact);
            unsigned u_tail_sz = r->get_uninterpreted_tail_size ();
            SASSERT (child_reach_facts.size () == u_tail_sz);
            for (unsigned i = 0; i < u_tail_sz; i++) {
                expr_ref ofml (m);
                child_pts.get (i)->get_manager ().formula_n2o 
                  (child_reach_facts[i]->get (), ofml, i);
                cex_ctx->assert_expr (ofml);
            }
            cex_ctx->assert_expr (pt->transition ());
            cex_ctx->assert_expr (pt->rule2tag (r));
            VERIFY (cex_ctx->check () == l_true);
            model_ref local_mdl;
            cex_ctx->get_model (local_mdl);
            cex_ctx->pop (1);

            model_evaluator mev (m, local_mdl);
            for (unsigned i = 0; i < child_pts.size (); i++) {
                pred_transformer& ch_pt = *(child_pts.get (i));
                unsigned sig_size = ch_pt.sig_size ();
                expr_ref_vector ground_fact_conjs (m);
                expr_ref_vector ground_arg_vals (m);
                for (unsigned j = 0; j < sig_size; j++) {
                    expr_ref sig_arg (m), sig_val (m);
                    sig_arg = m.mk_const (ch_pt.get_manager ().o2o (ch_pt.sig (j), 0, i));
                    if (m_params.use_heavy_mev ()) {
                        sig_val = mev.eval_heavy (sig_arg);
                    }
                    else {
                        sig_val = mev.eval (sig_arg);
                    }
                    ground_fact_conjs.push_back (m.mk_eq (sig_arg, sig_val));
                    ground_arg_vals.push_back (sig_val);
                }
                if (ground_fact_conjs.size () > 0) {
                    expr_ref ground_fact (m);
                    ground_fact = m.mk_and (ground_fact_conjs.size (), ground_fact_conjs.c_ptr ());
                    ch_pt.get_manager ().formula_o2n (ground_fact, ground_fact, i);
                    cex_facts.push_back (ground_fact);
                }
                else {
                    cex_facts.push_back (m.mk_true ());
                }
                cex.push_back (m.mk_app (ch_pt.head (), sig_size, ground_arg_vals.c_ptr ()));
            }
        }

        TRACE ("spacer",
                tout << "ground cex\n";
                for (unsigned i = 0; i < cex.size (); i++) {
                    tout << mk_pp (cex.get (i), m) << "\n";
                }
              );

        return expr_ref (m.mk_and (cex.size (), cex.c_ptr ()), m);
    }

    ///this is where everything starts
    lbool context::solve_core (unsigned from_lvl) 
    {
      //if there is no query predicate, abort
      if (!m_rels.find(m_query_pred, m_query)) return l_false;

      unsigned lvl = from_lvl;
      
      model_node *root = alloc (model_node, 0, *m_query, from_lvl, 0);
      root->set_post (m.mk_true ());
      m_search.set_root (*root);
      
      unsigned max_level = get_params ().pdr_max_level ();
      
      for (unsigned i = 0; i < max_level; ++i) {
        checkpoint();
        m_expanded_lvl = infty_level ();
        m_stats.m_max_query_lvl = lvl;

        if (check_reachability()) return l_true;
            
        if (lvl > 0 && !get_params ().pdr_skip_propagate ())
          if (propagate(m_expanded_lvl, lvl, UINT_MAX)) return l_false;
            
        m_search.inc_level ();
        lvl = m_search.max_level ();
        m_stats.m_max_depth = std::max(m_stats.m_max_depth, lvl);
        IF_VERBOSE(1,verbose_stream() << "Entering level "<< lvl << "\n";);
        IF_VERBOSE(1, 
                  if (m_params.print_statistics ()) {
                      statistics st;
                      collect_statistics (st);
                  };
                  );
      }
      return l_undef;
    }


    //
    bool context::check_reachability () 
    {
      timeit _timer (get_verbosity_level () >= 1, 
                     "spacer::context::check_reachability", 
                     verbose_stream ());

        model_node_ref last_reachable;
        
        if (get_params().reset_obligation_queue ()) m_search.reset ();
        
        unsigned initial_size = m_search.size ();
        unsigned restart_initial = 10;
        unsigned threshold = restart_initial;
        unsigned luby_idx = 1;
        
        while (m_search.top ())
        {
          model_node_ref node;
          checkpoint ();
          
          while (last_reachable)
          {
            checkpoint ();
            node = last_reachable;
            last_reachable = NULL;
            if (m_search.is_root (*node)) return true;
            if (expand_node (*node->parent ()) == l_true)
            {
              last_reachable = node->parent ();
              last_reachable->close ();
            }
          }
          
          SASSERT (m_search.top ());
          // -- remove all closed nodes and updated all dirty nodes
          // -- this is necessary because there is no easy way to
          // -- remove nodes from the priority queue.
          while (m_search.top ()->is_closed () ||
                 m_search.top ()->is_dirty ()) 
          { 
            model_node_ref n = m_search.top ();
            m_search.pop ();
            if (n->is_closed ())
            {
              IF_VERBOSE (1,
                          verbose_stream () << "Deleting closed node: " 
                          << n->pt ().head ()->get_name ()
                          << "(" << n->level () << ", " << n->depth () << ")"
                          << " " << n->post ()->get_id () << "\n";);
              if (m_search.is_root (*n)) return true;
              SASSERT (m_search.top ());
            }
            else if (n->is_dirty ())
            {
              n->clean ();
              // -- the node n might not be at the top after it is cleaned
              m_search.push (*n);
            }
            else 
              UNREACHABLE ();
          }
          
          SASSERT (m_search.top ());
          
          if (false && m_search.size () - initial_size > threshold)
          {
            luby_idx++;
            threshold = static_cast<unsigned>(get_luby(luby_idx)) * restart_initial;
            IF_VERBOSE (1, verbose_stream () 
                        << "(restarting :obligations " << m_search.size () 
                        << " :restart_threshold " << threshold
                        << ")\n";);
            m_search.reset ();
            initial_size = m_search.size ();
          }
          
          node = m_search.top ();
          SASSERT (node->level () <= m_search.max_level ());
          switch (expand_node (*node))
          {
          case l_true:
            SASSERT (m_search.top () == node.get ());
            m_search.pop ();
            last_reachable = node;
            last_reachable->close ();
            if (m_search.is_root (*node)) return true;
            break;
          case l_false:
            SASSERT (m_search.top () == node.get ());
            m_search.pop ();
            
            if (node->is_dirty ()) node->clean ();
            
            node->inc_level ();
            if (get_params ().pdr_flexible_trace () &&
                (node->level () >= m_search.max_level () || 
                 m_search.max_level () - node->level () 
                 <= get_params ().pdr_flexible_trace_depth ()))
              m_search.push (*node);
            
            if (m_search.is_root (*node)) return false;
            break;
          case l_undef:
            SASSERT (m_search.top () != node.get ());
            break;
          }
        }
        
        UNREACHABLE();
        return false;
    }

    //this processes a goal and creates sub-goal
    lbool context::expand_node(model_node& n) 
    {
      SASSERT(n.is_open());
      
      TRACE ("spacer", 
             tout << "expand-node: " << n.pt().head()->get_name() 
             << " level: " << n.level() 
             << " depth: " << (n.depth () - m_search.min_depth ()) << "\n"
             << mk_pp(n.post(), m) << "\n";);
      
      TRACE ("core_array_eq", 
             tout << "expand-node: " << n.pt().head()->get_name() 
             << " level: " << n.level() 
             << " depth: " << (n.depth () - m_search.min_depth ()) << "\n"
             << mk_pp(n.post(), m) << "\n";);
      
      stopwatch watch;
      IF_VERBOSE (1, verbose_stream () << "expand: " << n.pt ().head ()->get_name () 
                  << " (" << n.level () << ", " 
                  << (n.depth () - m_search.min_depth ()) << ") "
                  << (n.use_farkas_generalizer () ? "FAR " : "SUB ")
                  << n.post ()->get_id ();
                  verbose_stream().flush ();
                  watch.start (););
      

      // check the cache
      // DISABLED FOR NOW
      // if (n.pt().is_must_reachable (n.post())) {
      //     m_stats.m_num_reuse_reach++;
      //     n.set_reachable (true);
      // }
        
        
      // used in case n is unreachable
      unsigned uses_level = infty_level ();
      expr_ref_vector cube(m);
      model_ref model;
      
      // used in case n is reachable
      bool is_concrete;
      const datalog::rule * r = NULL;
      // denotes which predecessor's (along r) reach facts are used
      vector<bool> reach_pred_used; 
      unsigned num_reuse_reach = 0;

      
      if (get_params ().pdr_flexible_trace () && n.pt ().is_blocked (n, uses_level))
      {
        // if (!m_search.is_root (n)) n.close ();
        IF_VERBOSE (1, verbose_stream () << " K "
                    << std::fixed << std::setprecision(2) 
                    << watch.get_seconds () << "\n";);

        return l_false;
      }
      
      lbool res = expand_state(n, cube, model, uses_level, is_concrete, r, 
                         reach_pred_used, num_reuse_reach);
      checkpoint ();
      IF_VERBOSE (1, verbose_stream () << "." << std::flush;);
      switch (res) 
      {
        //reachable but don't know if this is purely using UA
      case l_true: {
        // update stats
        m_stats.m_num_reuse_reach += num_reuse_reach;

        model_evaluator mev (m, model);
        // must-reachable
        if (is_concrete) 
        {
          // -- update must summary
          if (r && r->get_uninterpreted_tail_size () > 0)
          {
            reach_fact* rf = mk_reach_fact (n, mev, *r);
            checkpoint ();
            n.pt ().add_reach_fact (*rf);
            checkpoint ();
          }
          
          // if n has a derivation, create a new child and report l_undef
          // otherwise if n has no derivation or no new children, report l_true
          model_node *next = NULL;
          if (n.has_derivation ())
          {
            next = n.get_derivation ().create_next_child ();
            checkpoint ();
            if (next) 
            { 
              // move derivation over to the next obligation
              next->set_derivation (n.detach_derivation ());
              
              // remove the current node from the queue if it is at the top
              if (m_search.top () == &n) m_search.pop ();
              
              m_search.push (*next);
            }
          }
          
          // -- close n, it is reachable
          // -- don't worry about remove n from the obligation queue
          n.close ();
          
          IF_VERBOSE(1, verbose_stream () << (next ? " X " : " T ")
                     << std::fixed << std::setprecision(2) 
                     << watch.get_seconds () << "\n";);
          return next ? l_undef : l_true;
        }
        
        // create a child of n
        create_children (n, *r, mev, reach_pred_used);
        IF_VERBOSE(1, verbose_stream () << " U "
                   << std::fixed << std::setprecision(2) 
                   << watch.get_seconds () << "\n";);
        return l_undef;
        
      }
        // n is unreachable, create new summary facts
      case l_false: {
        timeit _timer (is_trace_enabled("spacer_timeit"), 
                       "spacer::expand_node::false", 
                       verbose_stream ());

        // -- only update expanded level when new lemmas are generated at it.
        if (n.level() < m_expanded_lvl) m_expanded_lvl = n.level();

        TRACE("spacer", tout << "cube:\n"; 
              for (unsigned j = 0; j < cube.size(); ++j) 
                tout << mk_pp(cube[j].get(), m) << "\n";);

        core_generalizer::cores cores;
        cores.push_back (std::make_pair(cube, uses_level));
        
        // -- run all core generalizers
        for (unsigned i = 0; 
             // -- only generalize if lemma was constructed using farkas
             n.use_farkas_generalizer () && 
             !cores.empty() && i < m_core_generalizers.size(); 
             ++i) {
          checkpoint ();
          core_generalizer::cores new_cores;                    
          for (unsigned j = 0; j < cores.size(); ++j) 
            (*m_core_generalizers[i])(n, cores[j].first, cores[j].second, 
                                      new_cores);
          cores.reset ();
          cores.append (new_cores);
        }
        
        // -- convert cores into lemmas
        for (unsigned i = 0; i < cores.size(); ++i) {
          expr_ref_vector& core = cores[i].first;
          std::sort (core.c_ptr (), core.c_ptr () + core.size (), ast_lt_proc ());
          uses_level = cores[i].second;
          expr_ref lemma (m_pm.mk_not_and(core), m);
          TRACE("spacer", tout << "invariant state: " 
                << (is_infty_level(uses_level)?"(inductive)":"") 
                <<  mk_pp (lemma, m) << "\n";);
          bool v = n.pt().add_lemma (lemma, uses_level);
          // Optionally update the node to be the negation of the lemma
          if (v && get_params ().use_lemma_as_cti ())
          {
            n.new_post (m_pm.mk_and (core));
            n.set_farkas_generalizer (false);
          }
          CASSERT("spacer", n.level() == 0 || check_invariant(n.level()-1));
        }
        
        
        IF_VERBOSE(1, verbose_stream () << " F "
                   << std::fixed << std::setprecision(2) 
                   << watch.get_seconds () << "\n";);

        return l_false;
      }
        //something went wrong
      case l_undef: 
        TRACE("spacer", tout << "unknown state: " 
              << mk_pp(m_pm.mk_and(cube), m) << "\n";);
        throw unknown_exception();
      }
      UNREACHABLE();
      throw unknown_exception();
    }

    //
    // check if predicate transformer has a satisfiable predecessor state.
    // returns either a satisfiable predecessor state or 
    // return a property that blocks state and is implied by the 
    // predicate transformer (or some unfolding of it).
    // 
    lbool context::expand_state(model_node& n, expr_ref_vector& core, 
                                model_ref& model, 
                                unsigned& uses_level, bool& is_concrete, 
                                datalog::rule const*& r, vector<bool>& reach_pred_used, 
                                unsigned& num_reuse_reach) {
      return n.pt().is_reachable(n, &core, &model, uses_level, is_concrete, 
                                 r, reach_pred_used, num_reuse_reach);
    }

  bool context::propagate(unsigned min_prop_lvl, 
                          unsigned max_prop_lvl, unsigned full_prop_lvl) {    
    
    if (min_prop_lvl == infty_level ()) return false;
    
    timeit _timer (get_verbosity_level() >= 1, 
                   "spacer::context::propagate", 
                   verbose_stream ());
    
    if (full_prop_lvl < max_prop_lvl) full_prop_lvl = max_prop_lvl;
    
    if (m_params.pdr_simplify_formulas_pre()) {
      simplify_formulas();
    }
    IF_VERBOSE (1, verbose_stream () << "Propagating: " << std::flush;);
    
    for (unsigned lvl = min_prop_lvl; lvl <= full_prop_lvl; lvl++) {
      IF_VERBOSE (1, 
                  if (lvl > max_prop_lvl && lvl == max_prop_lvl + 1)
                    verbose_stream () << " ! ";
                  verbose_stream () << lvl << " " << std::flush;);

      checkpoint();
      CTRACE ("spacer", lvl > max_prop_lvl && lvl == max_prop_lvl + 1, 
              tout << "In full propagation\n";);
            
      bool all_propagated = true;
      decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
      for (; it != end; ++it) {
        checkpoint();            
        pred_transformer& r = *it->m_value;
        all_propagated = r.propagate_to_next_level(lvl) && all_propagated;
      }
      //CASSERT("spacer", check_invariant(lvl));

      if (all_propagated)
      {
        for (it = m_rels.begin (); it != end; ++it)
        {
          checkpoint ();
          pred_transformer& r = *it->m_value;
          r.propagate_to_infinity (lvl);
        }
        if (lvl <= max_prop_lvl)
        {
          m_inductive_lvl = lvl;
          IF_VERBOSE(1, verbose_stream () << "\n";);
          return true;
        }
        break;
      }
            
      if (all_propagated && lvl == max_prop_lvl) {
        m_inductive_lvl = lvl;
        return true;
      }
      else if (all_propagated && lvl > max_prop_lvl) break;
    }
    if (m_params.pdr_simplify_formulas_post()) {            
      simplify_formulas();
    }
    
    IF_VERBOSE(1, verbose_stream () << "\n";);
    return false;
  }

  reach_fact *context::mk_reach_fact (model_node& n, model_evaluator &mev,
                                      const datalog::rule& r) {
    timeit _timer1 (is_trace_enabled("spacer_timeit"), 
                    "mk_reach_fact", 
                    verbose_stream ());
        expr_ref res(m);
        reach_fact_ref_vector child_reach_facts;
        
        pred_transformer& pt = n.pt ();

        ptr_vector<func_decl> preds;
        pt.find_predecessors (r, preds);

        expr_ref_vector path_cons (m);
        path_cons.push_back (pt.get_transition (r));
        app_ref_vector vars (m);

        for (unsigned i = 0; i < preds.size (); i++) {
            func_decl* pred = preds[i];
            pred_transformer& ch_pt = get_pred_transformer (pred);
            // get a reach fact of body preds used in the model
            expr_ref o_ch_reach (m);
            reach_fact *kid = ch_pt.get_used_origin_reach_fact (mev, i);
            child_reach_facts.push_back (kid);
            m_pm.formula_n2o (kid->get (), o_ch_reach, i);
            path_cons.push_back (o_ch_reach);
            // collect o-vars to eliminate
            for (unsigned j = 0; j < pred->get_arity (); j++) 
                vars.push_back (m.mk_const (m_pm.o2o (ch_pt.sig (j), 0, i)));
            
            const ptr_vector<app> &v = kid->aux_vars (); 
            for (unsigned j = 0, sz = v.size (); j < sz; ++j)
              vars.push_back (m.mk_const (m_pm.n2o (v [j]->get_decl (), i)));
        }
        // collect aux vars to eliminate
        ptr_vector<app>& aux_vars = pt.get_aux_vars (r);
        bool elim_aux = get_params ().spacer_elim_aux ();
        if (elim_aux) vars.append (aux_vars.size (), aux_vars.c_ptr ());

        res = m_pm.mk_and (path_cons);
        
        // -- pick an implicant from the path condition
        if (get_params ().spacer_reach_dnf ())
        {
          expr_ref_vector u(m), lits(m);
          u.push_back (res);
          compute_implicant_literals (mev, u, lits);
          res = m_pm.mk_and (lits);
        }
        

        TRACE ("spacer",
                tout << "Reach fact, before QE:\n";
                tout << mk_pp (res, m) << "\n";
                tout << "Vars:\n";
                for (unsigned i = 0; i < vars.size(); ++i) {
                    tout << mk_pp(vars.get (i), m) << "\n";
                }
              );

        {
          timeit _timer1 (is_trace_enabled("spacer_timeit"), 
                          "mk_reach_fact::qe_project", 
                          verbose_stream ());
          qe_project (m, vars, res, mev.get_model ());
        }
        

        TRACE ("spacer",
                tout << "Reach fact, after QE project:\n";
                tout << mk_pp (res, m) << "\n";
                tout << "Vars:\n";
                for (unsigned i = 0; i < vars.size(); ++i) {
                    tout << mk_pp(vars.get (i), m) << "\n";
                }
              );

        SASSERT (vars.empty ());

        m_stats.m_num_reach_queries++;
        ptr_vector<app> empty;
        reach_fact *f = alloc(reach_fact, m, r, res, elim_aux ? empty : aux_vars);
        for (unsigned i = 0, sz = child_reach_facts.size (); i < sz; ++i)
          f->add_justification (*child_reach_facts [i]);
        return f;
    }


    /**
       \brief create children states from model cube.
    */
    void context::create_children(model_node& n, datalog::rule const& r, 
                                  model_evaluator &mev,
                                  const vector<bool> &reach_pred_used) {
 
        pred_transformer& pt = n.pt();
        expr* T   = pt.get_transition(r);
        expr* phi = n.post();

        TRACE("spacer", 
              tout << "Model:\n";
              model_smt2_pp(tout, m, *mev.get_model (), 0);
              tout << "\n";
              tout << "Transition:\n" << mk_pp(T, m) << "\n";
              tout << "Phi:\n" << mk_pp(phi, m) << "\n";);

        SASSERT (r.get_uninterpreted_tail_size () > 0);

        ptr_vector<func_decl> preds;
        pt.find_predecessors(r, preds);

        ptr_vector<pred_transformer> pred_pts;

        for (ptr_vector<func_decl>::iterator it = preds.begin ();
                it != preds.end (); it++) {
            pred_pts.push_back (&get_pred_transformer (*it));
        }

        expr_ref_vector forms(m), Phi(m);

        // obtain all formulas to consider for model generalization
        forms.push_back(T);
        forms.push_back(phi);

        compute_implicant_literals (mev, forms, Phi);
        
        //pt.remove_predecessors (Phi);

        app_ref_vector vars(m);
        unsigned sig_size = pt.head()->get_arity();
        for (unsigned i = 0; i < sig_size; ++i) {
            vars.push_back(m.mk_const(m_pm.o2n(pt.sig(i), 0)));
        }
        ptr_vector<app>& aux_vars = pt.get_aux_vars(r);
        vars.append(aux_vars.size(), aux_vars.c_ptr());

        expr_ref phi1 = m_pm.mk_and (Phi);
        qe_project (m, vars, phi1, mev.get_model (), true);
        //qe::reduce_array_selects (*mev.get_model (), phi1);
        SASSERT (vars.empty ());

        TRACE ("spacer",
                tout << "Literals\n";
                tout << mk_pp (m_pm.mk_and (Phi), m) << "\n";
                tout << "Reduced\n" << mk_pp (phi1, m) << "\n";
              );

        // expand literals. Ideally, we do not want to split aliasing
        // equalities. Unfortunately, the interface does not allow for
        // that yet.
        // XXX This mixes up with derivation. Needs more thought.
        // Phi.reset ();
        // qe::flatten_and (phi1, Phi);
        // if (!Phi.empty ())
        // {
        //   expand_literals (m, Phi);
        //   phi1 = m_pm.mk_and (Phi);
        // }
        
        
        /// create a derivation and populate it with premises
        derivation *deriv = alloc (derivation, n, r, phi1);
        for (unsigned i = 0, sz = preds.size (); i < sz; ++i)
        {
          unsigned j; 
          if (get_params ().order_children () == 1)
            // -- reverse order
            j = sz - i - 1;
          else 
            // -- default order
            j = i;
          
          pred_transformer &pt = get_pred_transformer (preds [j]);
          
          const ptr_vector<app> *aux = NULL;
          expr_ref sum(m);
          // XXX This is a bit confusing. The summary is returned over
          // XXX o-variables. But it is simpler if it is returned over n-variables instead.
          sum = pt.get_origin_summary (mev, prev_level (n.level ()),
                                       j, reach_pred_used [j], &aux);
          deriv->add_premise (pt, j, sum, reach_pred_used [j], aux);
        }
        
        // create post for the first child and add to queue
        model_node* kid = deriv->create_first_child (mev);
        SASSERT (kid);
        kid->set_derivation (deriv);
        
        // Optionally disable derivation optimization
        if (!get_params ().use_derivations ()) kid->reset_derivation ();
        
        m_search.push (*kid);
        m_stats.m_num_queries++;
    }




    void context::collect_statistics(statistics& st) const {
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (it = m_rels.begin(); it != end; ++it) {
            it->m_value->collect_statistics(st);
        }
        st.update("SPACER num queries", m_stats.m_num_queries);
        st.update("SPACER num reach queries", m_stats.m_num_reach_queries);
        st.update("SPACER num reuse reach facts", m_stats.m_num_reuse_reach);
        st.update("SPACER max query lvl", m_stats.m_max_query_lvl);
        st.update("SPACER max depth", m_stats.m_max_depth);
        st.update("SPACER inductive level", m_inductive_lvl);
        st.update("SPACER cex depth", m_stats.m_cex_depth);
        m_pm.collect_statistics(st);

        for (unsigned i = 0; i < m_core_generalizers.size(); ++i) {
            m_core_generalizers[i]->collect_statistics(st);
        }

        // brunch out
        verbose_stream () << "BRUNCH_STAT max_query_lvl " << m_stats.m_max_query_lvl << "\n";
        verbose_stream () << "BRUNCH_STAT num_queries " << m_stats.m_num_queries << "\n";
        verbose_stream () << "BRUNCH_STAT num_reach_queries " << m_stats.m_num_reach_queries << "\n";
        verbose_stream () << "BRUNCH_STAT num_reach_reuse " << m_stats.m_num_reuse_reach << "\n";
        verbose_stream () << "BRUNCH_STAT inductive_lvl " << m_inductive_lvl << "\n";
        verbose_stream () << "BRUNCH_STAT max_depth " << m_stats.m_max_depth << "\n";
        verbose_stream () << "BRUNCH_STAT cex_depth " << m_stats.m_cex_depth << "\n";
    }

    void context::reset_statistics() {
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (it = m_rels.begin(); it != end; ++it) {
            it->m_value->reset_statistics();
        }
        m_stats.reset();
        m_pm.reset_statistics();

        for (unsigned i = 0; i < m_core_generalizers.size(); ++i) {
            m_core_generalizers[i]->reset_statistics();
        }

    }


/*    std::ostream& context::display(std::ostream& out) const {
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (; it != end; ++it) {
            it->m_value->display(out);
        }        
        m_search.display(out);
        return out;
    }
*/

    bool context::check_invariant(unsigned lvl) {
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();        
        for (; it != end; ++it) {
            checkpoint();
            if (!check_invariant(lvl, it->m_key)) {
                return false;
            }
        }
        return true;
    }

    bool context::check_invariant(unsigned lvl, func_decl* fn) {
        smt::kernel ctx(m, m_fparams);
        pred_transformer& pt = *m_rels.find(fn);
        expr_ref_vector conj(m);
        expr_ref inv = pt.get_formulas(next_level(lvl), false);
        if (m.is_true(inv)) return true;
        pt.add_premises(m_rels, lvl, conj);
        conj.push_back(m.mk_not(inv));
        expr_ref fml(m.mk_and(conj.size(), conj.c_ptr()), m);
        ctx.assert_expr(fml);
        lbool result = ctx.check();
        TRACE("spacer", tout << "Check invariant level: " << lvl << " " << result << "\n" << mk_pp(fml, m) << "\n";);
        return result == l_false;
    }

    void context::display_certificate (std::ostream& strm) const { }

/*    void context::display_certificate(std::ostream& strm) const {
        switch(m_last_result) {
        case l_false: {
            expr_ref_vector refs(m);
            vector<relation_info> rs;
            get_level_property(m_inductive_lvl, refs, rs);    
            inductive_property ex(m, const_cast<model_converter_ref&>(m_mc), rs);
            strm << ex.to_string();
            break;
        }
        case l_true: {
            strm << mk_pp(mk_sat_answer(), m);
            break;
        }
        case l_undef: {
            strm << "unknown";
            break;
        }
        }
    }
*/

  expr_ref context::get_constraints (unsigned level)
  {
    expr_ref res(m);
    expr_ref_vector constraints(m);

    decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
    for (; it != end; ++it) {
      pred_transformer& r = *it->m_value;
      expr_ref c = r.get_formulas(level, false);

      if (m.is_true(c)) continue;

      // replace local constants by bound variables.
      expr_ref_vector args(m);
      for (unsigned i = 0; i < r.sig_size(); ++i) 
        args.push_back(m.mk_const(m_pm.o2n(r.sig(i), 0)));

      expr_ref pred(m);
      pred = m.mk_app(r.head (), r.sig_size(), args.c_ptr());

      constraints.push_back(m.mk_implies(pred, c));
    }

    if (constraints.empty ()) return expr_ref (m.mk_true (), m);
    return m_pm.mk_and (constraints);
  }
  
  void context::add_constraints (unsigned level, expr_ref c)
  {
    if (!c.get ()) return;
    if (m.is_true (c)) return;
    
    expr_ref_vector constraints (m);
    constraints.push_back (c);
    qe::flatten_and (constraints);
    
    for (unsigned i = 0, sz = constraints.size (); i < sz; ++i)
    {
      expr *c = constraints.get (i);
      expr *e1, *e2;
      if (m.is_implies (c, e1, e2))
      {
        SASSERT (is_app (e1));
        pred_transformer *r = 0;
        if (m_rels.find (to_app (e1)->get_decl (), r))
          r->add_lemma (e2, level);
      }
    }
  }
  

  inline bool model_node_lt::operator() (const model_node *pn1, const model_node *pn2) const
  {
    SASSERT (pn1);
    SASSERT (pn2);
    const model_node& n1 = *pn1; 
    const model_node& n2 = *pn2;
      
    if (n1.level () != n2.level ()) return n1.level () < n2.level ();
      
    if (n1.depth () != n2.depth ()) return n1.depth () < n2.depth ();
    
    // -- a more deterministic order of proof obligations in a queue
    // if (!n1.get_context ().get_params ().spacer_nondet_tie_break ())
    {
      const expr* p1 = n1.post ();
      const expr* p2 = n2.post ();
      ast_manager &m = n1.get_ast_manager ();
      
      
      // -- order by size. Less conjunctions is a proxy for
      // -- generality.  Currently, this takes precedence over
      // -- predicates which might not be the best choice
      unsigned sz1 = 1;
      unsigned sz2 = 1;
      
      if (m.is_and (p1)) sz1 = to_app (p1)->get_num_args ();
      if (m.is_and (p2)) sz2 = to_app (p2)->get_num_args ();
      if (sz1 != sz2) return sz1 < sz2;
      
      // -- when all else fails, order by identifiers of the
      // -- expressions.  This roughly means that expressions created
      // -- earlier are preferred.  Note that variables in post are
      // -- based on names of the predicates. Hence this guarantees an
      // -- order over predicates as well. That is, two expressions
      // -- are equal if and only if they correspond to the same proof
      // -- obligation of the same predicate.
      if (p1->get_id () != p2->get_id ()) return p1->get_id () < p2->get_id ();
      
      if (n1.pt ().head ()->get_id () == n2.pt ().head ()->get_id ())
      {
        IF_VERBOSE (1, 
                    verbose_stream () 
                    << "dup: " << n1.pt ().head ()->get_name () 
                    << "(" << n1.level () << ", " << n1.depth () << ") " 
                    << p1->get_id () << "\n";
                    //<< " p1: " << mk_pp (const_cast<expr*>(p1), m) << "\n"
                    );
      }
      
      // XXX see comment below on identical nodes
      // SASSERT (n1.pt ().head ()->get_id () != n2.pt ().head ()->get_id ());
      // -- if expression comparison fails, compare by predicate id
      if (n1.pt().head ()->get_id () != n2.pt ().head ()->get_id ())
        return n1.pt ().head ()->get_id () < n2.pt ().head ()->get_id ();
      
      /** XXX Identical nodes. This should not happen. However,
       * currently, when propagating reachability, we might call
       * expand_node() twice on the same node, causing it to generate
       * the same proof obligation multiple times */
      return &n1 < &n2;
    }
    // else
    //   return &n1 < &n2;
  }

  
  
}
