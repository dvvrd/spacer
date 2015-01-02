/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_context.cpp

Abstract:

    SPACER predicate transformers and search context.

Author:

    Anvesh Komuravelli

Revision History:

    Based on ../pdr/pdr_context.cpp by
     Nikolaj Bjorner (nbjorner)

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

namespace spacer {
    
    // ----------------
    // pred_tansformer

    pred_transformer::pred_transformer(context& ctx, manager& pm, func_decl* head): 
        pm(pm), m(pm.get_manager()),
        ctx(ctx), m_head(head, m), 
        m_sig(m), m_solver(pm, ctx.get_params(), head->get_name(), ctx.get_params ().validate_theory_core ()),
        m_reach_ctx (pm.mk_fresh ()),
        m_reach_facts (m), m_invariants(m), m_transition(m), m_initial_state(m), 
        m_all_init (false),
        m_reach_case_vars (m)
    { init_sig (); }

    pred_transformer::~pred_transformer() {
        rule2inst::iterator it2 = m_rule2inst.begin(), end2 = m_rule2inst.end();
        for (; it2 != end2; ++it2) {
            dealloc(it2->m_value);
        }
        rule2expr::iterator it3 = m_rule2transition.begin(), end3 = m_rule2transition.end();
        for (; it3 != end3; ++it3) {
            m.dec_ref(it3->m_value);
        }
        obj_map<expr, reach_fact_just*>::iterator it4 = m_reach_fact_justs.begin (), end4 = m_reach_fact_justs.end ();
        for (; it4 != end4; it4++) {
            dealloc (it4->m_value);
        }
    }

    std::ostream& pred_transformer::display(std::ostream& out) const {
        if (!rules().empty()) out << "rules\n";
        for (unsigned i = 0; i < rules().size(); ++i) {
            rules()[i]->display_smt2(m, out) << "\n";
        }        
        out << "transition\n" << mk_pp(transition(), m) << "\n";
        return out;
    }

    void pred_transformer::collect_statistics(statistics& st) const {
        m_solver.collect_statistics(st);
        //m_reachable.collect_statistics(st);
        st.update("SPACER num propagations", m_stats.m_num_propagations);
        unsigned np = m_invariants.size();
        for (unsigned i = 0; i < m_levels.size(); ++i) {
            np += m_levels[i].size();
        } 
        st.update("SPACER num properties", np); 
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
        if (is_infty_level(level)) {
            return;
        }
        while (m_levels.size() <= level) {
            m_solver.add_level();
            m_levels.push_back(expr_ref_vector(m));
        }
    }

    bool pred_transformer::is_reachable_known (expr* state, model_ref* model) {
        SASSERT (state);
        // XXX This seems to mis-handle the case when state is
        // reachable using the init rule of the current transformer
        if (m_reach_facts.empty ()) return false;
        
        m_reach_ctx->push ();
        m_reach_ctx->assert_expr (state);
        expr_ref_vector assumps (m);
        assumps.push_back (m.mk_not (m_reach_case_vars.back ()));
        // XXX why use check-with-assumptions here?
        lbool res = m_reach_ctx->check (assumps);
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
  
  void pred_transformer::get_used_reach_fact (model_evaluator& mev, expr_ref& reach_fact) {
    expr_ref v (m);
    
    for (unsigned i = 0, sz = m_reach_case_vars.size (); i < sz; i++) {
      v = mev.eval (m_reach_case_vars.get (i));
      if (m.is_false (v)) {
        reach_fact = m_reach_facts.get (i);
        break;
      }
    }
    
    SASSERT (reach_fact);
  }
  
  void pred_transformer::get_used_origin_reach_fact (model_evaluator& mev, unsigned oidx, 
                                                     expr_ref& res) {
    expr_ref b(m), v(m);
    
    for (unsigned i = 0, sz = m_reach_case_vars.size (); i < sz; i++) {
      v = m_reach_case_vars.get (i);
      pm.formula_n2o (v.get (), v, oidx);
      b = mev.eval (v);
      
      if (m.is_false (b)) {
        res = m_reach_facts.get (i);
        break;
      }
    }
    SASSERT (res);
  }

    datalog::rule const* pred_transformer::get_just_rule (expr* fact) {
        reach_fact_just* j = m_reach_fact_justs.find (fact);
        TRACE ("spacer", tout << "justification: " << j << "\n";);
        return &(j->r);
    }

    expr_ref_vector const* pred_transformer::get_just_pred_facts (expr* fact) {
        reach_fact_just* j = m_reach_fact_justs.find (fact);
        return &(j->pred_reach_facts);
    }

    datalog::rule const* pred_transformer::find_rule(model &model, 
                                                     bool& is_concrete, 
                                                     vector<bool>& reach_pred_used, 
                                                     unsigned& num_reuse_reach) {
        typedef obj_map<expr, datalog::rule const*> tag2rule;
        TRACE ("spacer_verbose",
                tag2rule::iterator it = m_tag2rule.begin();
                tag2rule::iterator end = m_tag2rule.end();
                for (; it != end; ++it) {
                    expr* pred = it->m_key;
                    tout << mk_pp(pred, m) << ":\n";
                    if (it->m_value) it->m_value->display_smt2(m, tout) << "\n";                  
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
                    expr_ref reach_var (pt.get_last_reach_case_var (), m);
                    if (!reach_var) is_concrete = false;
                    else {
                      pm.formula_n2o (reach_var.get (), reach_var, i);
                      model.eval (to_app (reach_var.get ())->get_decl (), vl);
                      used = m.is_false (vl);
                      is_concrete = is_concrete && used;
                    }

                    reach_pred_used.push_back (used);
                    if (used) num_reuse_reach++;
                }
                if (is_concrete) break;
            }
        }
        VERIFY (r);
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

    void pred_transformer::simplify_formulas(tactic& tac, expr_ref_vector& v) {
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

    void pred_transformer::simplify_formulas() {
        tactic_ref us = mk_unit_subsumption_tactic(m);
        simplify_formulas(*us, m_invariants);
        for (unsigned i = 0; i < m_levels.size(); ++i) {
            simplify_formulas(*us, m_levels[i]);
        }             
    }

    expr_ref pred_transformer::get_formulas(unsigned level, bool add_axioms) {
        expr_ref_vector res(m);
        if (add_axioms) {
            res.push_back(pm.get_background());
            res.push_back((level == 0)?initial_state():transition());
        }
        res.append(m_invariants);
        for (unsigned i = level; i < m_levels.size(); ++i) {
            res.append(m_levels[i]);
        }     
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

    bool pred_transformer::propagate_to_next_level(unsigned src_level) {
      
      if (m_levels.size () <= src_level) return true;
      if (m_levels [src_level].empty ()) return true;
      
        unsigned tgt_level = next_level(src_level);
        ensure_level(next_level(tgt_level));
        expr_ref_vector& src = m_levels[src_level];
        

        CTRACE("spacer", !src.empty(), 
               tout << "propagating " << src_level << " to " << tgt_level;
               tout << " for relation " << head()->get_name() << "\n";);
                
        for (unsigned i = 0; i < src.size(); ) {
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
            else if (is_invariant(tgt_level, curr, false, solver_level)) {
              
                add_property(curr, solver_level);
                TRACE("spacer", tout << "is invariant: "<< pp_level(solver_level) << " " << mk_pp(curr, m) << "\n";);              
                src[i] = src.back();
                src.pop_back();
                ++m_stats.m_num_propagations;
            }
            else {
                TRACE("spacer", tout << "not propagated: " << mk_pp(curr, m) << "\n";); 
                ++i;
            }
        }        
        IF_VERBOSE(3, verbose_stream() << "propagate: " << pp_level(src_level) << "\n";
                   for (unsigned i = 0; i < src.size(); ++i) {
                       verbose_stream() << mk_pp(src[i].get(), m) << "\n";   
                   });
        CTRACE ("spacer", src.empty (), 
                tout << "Fully propagated level " 
                << src_level << " of " << head ()->get_name () << "\n";);
        
        return src.empty();
    }

    bool pred_transformer::add_property1(expr * lemma, unsigned lvl) {        
        if (is_infty_level(lvl)) {
            if (!m_invariants.contains(lemma)) {
                TRACE("spacer", tout << "property1: " 
                      << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
                m_invariants.push_back(lemma);
                m_prop2level.insert(lemma, lvl);
                m_solver.add_formula(lemma);
                return true;
            }
            
            TRACE("spacer", tout << "already contained: " 
                  << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
            return false;
        }
        
        ensure_level(lvl);        
        unsigned old_level;
        if (!m_prop2level.find(lemma, old_level) || old_level < lvl) {
            TRACE("spacer", tout << "property1: " << pp_level(lvl) 
                  << " " << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
            m_levels[lvl].push_back(lemma);
            m_prop2level.insert(lemma, lvl);
            m_solver.add_level_formula(lemma, lvl);
            return true;
        }
        
        TRACE("spacer", tout << "old-level: " << pp_level(old_level) 
              << " " << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
        return false;
    }

    void pred_transformer::add_child_property(pred_transformer& child, 
                                              expr* lemma, unsigned lvl) {
      ensure_level(lvl);
      expr_ref_vector fmls(m);
      mk_assumptions(child.head(), lemma, fmls);
      for (unsigned i = 0; i < fmls.size(); ++i) {
        TRACE("spacer_detail", tout << "child property: " << mk_pp(fmls[i].get(), m) << "\n";);
        if (is_infty_level(lvl)) 
          m_solver.add_formula(fmls[i].get());
        else 
          m_solver.add_level_formula(fmls[i].get(), lvl);
      }
    }

    void pred_transformer::add_property(expr* lemma, unsigned lvl) {
        expr_ref_vector lemmas(m);
        qe::flatten_and(lemma, lemmas);
        for (unsigned i = 0; i < lemmas.size(); ++i) {
            expr* lemma_i = lemmas[i].get();
            if (add_property1(lemma_i, lvl)) {
                IF_VERBOSE(2, verbose_stream() << pp_level(lvl) << " " 
                           << mk_pp(lemma_i, m) << "\n";);
                for (unsigned j = 0; j < m_use.size(); ++j) {
                    m_use[j]->add_child_property(*this, lemma_i, next_level(lvl));
                }
            }
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

    unsigned pred_transformer::get_num_reach_vars () const 
    {return m_reach_case_vars.size ();}

    void pred_transformer::add_reach_fact (expr* fact, datalog::rule const& r, 
                                           expr_ref_vector const& child_reach_facts) 
    {
      TRACE ("spacer",
             tout << "add_reach_fact: " << head()->get_name() << " " 
             << mk_pp(fact, m) << "\n";);

      m_reach_facts.push_back (fact);
      reach_fact_just* j = alloc (reach_fact_just, r, child_reach_facts);
      m_reach_fact_justs.insert (fact, j);

      // update m_reach_ctx
      expr_ref last_var (m);
      expr_ref new_var (m);
      expr_ref fml (m);
      
      if (!m_reach_case_vars.empty ()) last_var = m_reach_case_vars.back ();
      new_var = mk_fresh_reach_case_var ();
      if (last_var)
        fml = m.mk_or (m.mk_not (last_var), fact, new_var);
      else
        fml = m.mk_or (fact, new_var);
      
      m_reach_ctx->assert_expr (fml);
      TRACE ("spacer",
             tout << "updating reach ctx: " << mk_pp(fml, m) << "\n";);

      // update users; reach facts are independent of levels
      for (unsigned i = 0; i < m_use.size(); ++i) {
        m_use[i]->add_child_property (*this, fml, infty_level ());
      }
    }

    expr* pred_transformer::get_reach () {
        if (m_reach_facts.empty ()) {
            return m.mk_false ();
        }
        return m.mk_or (m_reach_facts.size (), m_reach_facts.c_ptr ());
    }

  expr* pred_transformer::get_last_reach_case_var () const 
  {
    return m_reach_case_vars.empty () ? NULL : m_reach_case_vars.back ();
  }
  
    expr_ref pred_transformer::get_cover_delta(func_decl* p_orig, int level) {
        expr_ref result(m.mk_true(), m), v(m), c(m);
        if (level == -1) {
            result = pm.mk_and(m_invariants);                       
        }
        else if ((unsigned)level < m_levels.size()) {
            result = pm.mk_and(m_levels[level]);
        }
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
                                                 bool must)
  {
    expr_ref_vector summary (m);
    expr_ref v(m);
    
    if (!must) // use may summary
      summary.push_back (get_formulas (level, false));
    else // find must summary to use
    {
      get_used_origin_reach_fact (mev, oidx, v);
      summary.push_back (v);
      v.reset ();
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
        add_property(result, level);        
    }

    void  pred_transformer::propagate_to_infinity(unsigned level) {
      TRACE ("spacer", tout << "propagating to oo from lvl " << level 
             << " of " << head ()->get_name () << "\n";);
      
        for (unsigned i = m_levels.size () - 1; i >= level; --i)
        {
          expr_ref_vector &lemmas = m_levels [i];
          for (unsigned j = 0; j < lemmas.size (); ++j)
            add_property(lemmas[j].get (), infty_level ());
          lemmas.reset();
        }
    }

  lbool pred_transformer::is_reachable(model_node& n, expr_ref_vector* core, 
                                       model_ref* model, unsigned& uses_level, 
                                         bool& is_concrete, datalog::rule const*& r, 
                                       vector<bool>& reach_pred_used, 
                                       unsigned& num_reuse_reach) {
        TRACE("spacer", 
              tout << "is-reachable: " << head()->get_name() << " level: " 
              << n.level() << "\n";
              tout << mk_pp(n.post(), m) << "\n";);

        ensure_level(n.level());        

        // prepare the solver
        prop_solver::scoped_level _sl(m_solver, n.level());
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
                    expr_ref a (pt.get_last_reach_case_var (), m);
                    if (a) 
                    {
                      pm.formula_n2o (a.get (), a, i);
                      reach_assumps.push_back (m.mk_not (a));
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
        lbool is_sat = m_solver.check_assumptions (post, reach_assumps);

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
            TRACE ("spacer", tout << "reachable\n";);
            SASSERT ((bool)model);
            r = find_rule (**model, is_concrete, reach_pred_used, num_reuse_reach);
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

    bool pred_transformer::is_invariant(unsigned level, expr* states, bool inductive, unsigned& solver_level, expr_ref_vector* core) {
        expr_ref_vector conj(m);
        expr_ref tmp(m);
        
        conj.push_back(m.mk_not(states));

        if (inductive) {
            mk_assumptions(head(), states, conj);
        }
        tmp = pm.mk_and(conj);
        prop_solver::scoped_level _sl(m_solver, level);
        m_solver.set_core(core);
        m_solver.set_model(0);
        lbool r = m_solver.check_conjunction_as_assumptions(tmp);
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
        expr_ref fml(m), states(m);
        states = m.mk_not(pm.mk_and(lits));
        mk_assumptions(head(), states, conj);
        fml = pm.mk_and(conj);
        prop_solver::scoped_level _sl(m_solver, level);
        m_solver.set_core(&core);
        m_solver.set_subset_based_core(true);
        expr_ref_vector aux (m);
        lbool res = m_solver.check_assumptions_and_formula(lits, aux, fml);
        if (res == l_false) {
            lits.reset();
            lits.append(core);
            uses_level = m_solver.uses_level();
        }
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
            transitions.push_back(pred);
            transition = pm.mk_and(transitions);
            // mk init condition
            if (!is_init[0]) {
                init_conds.push_back (m.mk_not (pred));
            }
            break;
        default:
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
            ground_free_vars(rule.get_tail(i), var_reprs, aux_vars);
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
        if (ctx.is_dl() || ctx.is_utvpi()) {
            hoist_non_bool_if(fml);
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
    void pred_transformer::ground_free_vars(expr* e, app_ref_vector& vars, ptr_vector<app>& aux_vars) {
        ptr_vector<sort> sorts;
        get_free_vars(e, sorts);
        while (vars.size() < sorts.size()) {
            vars.push_back(0);
        }
        for (unsigned i = 0; i < sorts.size(); ++i) {
            if (sorts[i] && !vars[i].get()) {
                vars[i] = m.mk_fresh_const("aux", sorts[i]);
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
        SASSERT(m_head == other.m_head);
        obj_map<expr, unsigned>::iterator it  = other.m_prop2level.begin();
        obj_map<expr, unsigned>::iterator end = other.m_prop2level.end();        
        for (; it != end; ++it) {
            add_property(it->m_key, it->m_value);
        }
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
                                     expr *summary, bool must) : 
    m_pt (pt), m_oidx (oidx), 
    m_summary (summary, pt.get_ast_manager ()), m_must (must),
    m_ovars (pt.get_ast_manager ())
  {
    
    ast_manager &m = m_pt.get_ast_manager ();
    manager &sm = m_pt.get_manager ();
    
    unsigned sig_sz = m_pt.head ()->get_arity ();
    for (unsigned i = 0; i < sig_sz; ++i)
      m_ovars.push_back (m.mk_const (sm.o2o (pt.sig (i), 0, m_oidx)));
  }
  
  derivation::premise::premise (const derivation::premise &p) :
    m_pt (p.m_pt), m_oidx (p.m_oidx), m_summary (p.m_summary), m_must (p.m_must),
    m_ovars (p.m_ovars) {}
  
  
  void derivation::add_premise (pred_transformer &pt, 
                                unsigned oidx,
                                expr* summary,
                                bool must)
  {m_premises.push_back (premise (pt, oidx, summary, must));}
  


  model_node *derivation::create_first_child (model_evaluator &mev)
  {
    if (m_premises.empty ()) return NULL;
    m_active = 0;
    return create_next_child (mev);
  }
  
  model_node *derivation::create_next_child (model_evaluator &mev)
  {
    
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
      qe_project (m, vars, m_trans, mev.get_model ());
      qe::reduce_array_selects (*mev.get_model (), m_trans);
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
      qe_project (m, vars, post, mev.get_model ());
      qe::reduce_array_selects (*mev.get_model (), post);
    }
    
    get_manager ().formula_o2n (post.get (), post, m_premises [m_active].get_oidx ());
    
    model_node *n = alloc (model_node, &m_parent, 
                           m_premises[m_active].pt (), 
                           prev_level (m_parent.level ()));
    n->set_post (post);
    return n;
  }
  
  model_node *derivation::create_next_child ()
  {
    if (m_active >= m_premises.size ()) return NULL;
    
    // update the summary of the active node to some must summary
    
    // construct a new model consistent with the must summary of m_active premise
    pred_transformer &pt = m_premises[m_active].pt ();
    model_ref model;
    
    ast_manager &m = get_ast_manager ();
    expr_ref_vector summaries (m);
    
    for (unsigned i = m_active + 1; i < m_premises.size (); ++i)
      summaries.push_back (m_premises [i].get_summary ());
    
    // -- orient transition relation towards m_active premise
    expr_ref v(m);
    get_manager ().formula_o2n (m_trans, v, m_premises[m_active].get_oidx (), false);
    summaries.push_back (v);
    
    /// must be true, otherwise no suitable must summary found
    VERIFY (pt.is_reachable_known (get_manager ().mk_and (summaries), &model));
    
    model_evaluator mev (m, model);
    // find must summary used
    pt.get_used_reach_fact (mev, v);
    
    // get an implicant of the summary
    expr_ref_vector u(m), lits (m);
    u.push_back (v);
    compute_implicant_literals (mev, u, lits);
    v = get_manager ().mk_and (lits);
    
    expr_ref s(m);
    get_manager ().formula_n2o (v, s, m_premises[m_active].get_oidx ());
    m_premises[m_active].set_summary (s, true);
    
    return create_next_child (mev);
  }
  
    // ----------------
    // model_search

  model_node* model_search::next () {
    if (m_leaves.empty ()) return NULL;
      
    model_node* result = m_leaves.top ();
    m_leaves.pop ();
    return result;
  }

    void model_search::set_root (model_node& root) {
        reset();
        m_root = &root;
        enqueue_leaf(root);
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
  
    model_search::~model_search() {reset();}

    void model_search::reset() {
        while (!m_leaves.empty ()) m_leaves.pop ();
        m_root = NULL;
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
          m_pm(m_fparams, params.max_num_contexts(), m),
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
        if (!m_params.validate_result()) return true;
        
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
                    TRACE ("spacer", r.display_smt2(m, tout) << "\n";);
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
                    ptr_vector<sort> sorts;
                    svector<symbol> names;
                    get_free_vars(tmp, sorts);
                    for (unsigned i = 0; i < sorts.size(); ++i) {
                        if (!sorts[i]) {
                            sorts[i] = m.mk_bool_sort();
                        }
                        names.push_back(symbol(i));
                    }
                    sorts.reverse();
                    if (!sorts.empty()) {
                        tmp = m.mk_exists(sorts.size(), sorts.c_ptr(), names.c_ptr(), tmp);
                    }
                    smt::kernel solver(m, get_fparams());
                    solver.assert_expr(tmp);
                    lbool res = solver.check();
                    if (res != l_false) {
                        msg << "rule validation failed when checking: " << mk_pp(tmp, m);
                        IF_VERBOSE(0, verbose_stream() << msg.str() << "\n";);
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
        bool use_mc = m_params.use_multicore_generalizer();
        if (use_mc) {
            m_core_generalizers.push_back(alloc(core_multi_generalizer, *this, 0));
        }
        if (m_params.use_farkas() && !classify.is_bool()) {
            m.toggle_proof_mode(PGM_FINE);
            m_fparams.m_arith_bound_prop = BP_NONE;
            m_fparams.m_arith_auto_config_simplex = true;
            m_fparams.m_arith_propagate_eqs = false;
            m_fparams.m_arith_eager_eq_axioms = false;
            if (m_params.use_utvpi()) {
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
        if (!use_mc && m_params.use_inductive_generalizer()) {
            m_core_generalizers.push_back(alloc(core_bool_inductive_generalizer, *this, 0));
        }
        if (m_params.inductive_reachability_check()) {
            m_core_generalizers.push_back(alloc(core_induction_generalizer, *this));
        }
        if (m_params.use_arith_inductive_generalizer()) {
            m_core_generalizers.push_back(alloc(core_arith_inductive_generalizer, *this));
        }
        
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
      if (solve_core (from_lvl))
      {        
        //IF_VERBOSE(1, verbose_stream() << "\n"; m_search.display(verbose_stream()););  
        m_last_result = l_true;
      }
      else 
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
        expr_ref_vector facts (m);

        // temporary
        expr_ref fact (m);
        datalog::rule const* r;
        pred_transformer* pt;

        // get and discard query rule
        fact = m.mk_true ();
        r = m_query->get_just_rule (fact);

        // initialize queues
        // assume that the query is only on a single predicate
        // (i.e. disallow fancy queries for now)
        facts.append (*(m_query->get_just_pred_facts (fact)));
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
            r = pt->get_just_rule (fact);
            rules.push_back (const_cast<datalog::rule *> (r));
            TRACE ("spacer",
                    tout << "next rule: " << r->name ().str () << "\n";
                  );
            // add child facts and pts
            facts.append (*(pt->get_just_pred_facts (fact)));
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
        expr_ref_vector reach_facts (m);
        ptr_vector<func_decl> preds;
        ptr_vector<pred_transformer> pts;
        expr_ref_vector cex (m), // pre-order list of ground instances of predicates
                        cex_facts (m); // equalities for the ground cex using signature constants

        // temporary
        expr_ref reach_fact (m);
        pred_transformer* pt;
        expr_ref cex_fact (m);
        datalog::rule const* r;

        // get and discard query rule
        reach_fact = m.mk_true ();
        r = m_query->get_just_rule (reach_fact);

        // initialize queues
        reach_facts.append (*(m_query->get_just_pred_facts (reach_fact)));
        SASSERT (reach_facts.size () == 1);
        m_query->find_predecessors (*r, preds);
        SASSERT (preds.size () == 1);
        pts.push_back (&(get_pred_transformer (preds[0])));
        cex_facts.push_back (m.mk_true ());
        cex.push_back (m.mk_const (preds[0]));

        // smt context to obtain local cexes
        scoped_ptr<smt::kernel> cex_ctx = alloc (smt::kernel, m, get_fparams ());
        model_evaluator mev (m);

        // preorder traversal of the query derivation tree
        for (unsigned curr = 0; curr < pts.size (); curr++) {
            // pick next pt, fact, and cex_fact
            pt = pts.get (curr);
            reach_fact = reach_facts.get (curr);
            cex_fact = cex_facts.get (curr);

            expr_ref_vector const* child_reach_facts;
            ptr_vector<pred_transformer> child_pts;

            // get justifying rule and child facts for the derivation of reach_fact at pt
            r = pt->get_just_rule (reach_fact);
            child_reach_facts = pt->get_just_pred_facts (reach_fact);
            // get child pts
            preds.reset (); pt->find_predecessors (*r, preds);
            for (unsigned j = 0; j < preds.size (); j++) {
                child_pts.push_back (&(get_pred_transformer (preds[j])));
            }
            // update the queues
            reach_facts.append (*child_reach_facts);
            pts.append (child_pts);

            // update cex and cex_facts by making a local sat check:
            // check consistency of reach facts of children, rule body, and cex_fact
            cex_ctx->push ();
            cex_ctx->assert_expr (cex_fact);
            unsigned u_tail_sz = r->get_uninterpreted_tail_size ();
            SASSERT (child_reach_facts->size () == u_tail_sz);
            for (unsigned i = 0; i < u_tail_sz; i++) {
                expr_ref ofml (m);
                child_pts.get (i)->get_manager ().formula_n2o (child_reach_facts->get (i), ofml, i);
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
    bool context::solve_core (unsigned from_lvl) 
    {
      //if there is no query predicate, abort
      if (!m_rels.find(m_query_pred, m_query)) return false;

      unsigned lvl = from_lvl; //this is stack depth bound
      while (true) {
        checkpoint();
        m_expanded_lvl = lvl;
        m_stats.m_max_query_lvl = lvl;

        if (check_reachability(lvl)) return true;
            
        if (lvl > 0 && propagate(m_expanded_lvl, lvl, UINT_MAX)) return false;
            
        lvl++;
        m_stats.m_max_depth = std::max(m_stats.m_max_depth, lvl);
        IF_VERBOSE(1,verbose_stream() << "Entering level "<<lvl << "\n";);
      }
    }


    //
    // Pick a potential counter example state.
    // Initialize a search tree using that counter-example.
    // If the counter-example expands to a full model, then
    // the search tree is a model, otherwise obtain the next
    // query state.
    //
    bool context::check_reachability(unsigned level) 
    {
        expr_ref post (m.mk_true(), m);

        //create the initial goal -- this is the INIT rule
        model_node* root = alloc (model_node, 0, *m_query, level);
        root->set_post (post);
        m_search.set_root(*root);            
        
        while (model_node* node = m_search.next ()) 
        {
            IF_VERBOSE(2, 
                       verbose_stream() << "Expand node: " 
                       << node->level() << "\n";);
            checkpoint();
            
            // -- if a node has a derivation, either close it or derive a child
            if (node->has_derivation ())
            {
              model_node *kid = node->get_derivation ().create_next_child ();
              if (kid) 
              {
                m_search.enqueue_leaf (*kid);
                continue;
              }
              else
                node->reset_derivation ();
            }
            
            SASSERT (!node->has_derivation ());
            expand_node (*node);   
        }
        return root->is_reachable ();
    }

    //this processes a goal and creates sub-goal
    void context::expand_node(model_node& n) 
    {
      SASSERT(n.is_open());
      
      if (n.level() < m_expanded_lvl) m_expanded_lvl = n.level();

      TRACE ("spacer", 
             tout << "expand-node: " << n.pt().head()->get_name() 
             << " level: " << n.level() << "\n";
             tout << mk_pp(n.post(), m) << "\n";);

      // check the cache
      // DISABLED FOR NOW
      // if (n.pt().is_reachable_known (n.post())) {
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

      switch (expand_state(n, cube, model, uses_level, is_concrete, r, 
                           reach_pred_used, num_reuse_reach)) 
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
          expr_ref reach_fact (m);
          expr_ref_vector child_reach_facts (m);
          mk_reach_fact (n, mev, *r, reach_fact, child_reach_facts);
          n.pt ().add_reach_fact (reach_fact, *r, child_reach_facts);
          
          if (n.is_root ()) n.set_reachable (true);
          else
          {
            dealloc (&n);
            m_search.enqueue_leaf (*n.parent ());
          }
          
        }
        //otherwise pick the first OA and create a sub-goal
        else 
          create_children (n, *r, mev, reach_pred_used);
        break;
      }
        // n is unreachable, create new summary facts
      case l_false: {
        TRACE("spacer", tout << "cube:\n"; 
              for (unsigned j = 0; j < cube.size(); ++j) 
                tout << mk_pp(cube[j].get(), m) << "\n";);

        core_generalizer::cores cores;
        cores.push_back (std::make_pair(cube, uses_level));
        
        // -- run all core generalizers
        for (unsigned i = 0; !cores.empty() && i < m_core_generalizers.size(); ++i) {
          core_generalizer::cores new_cores;                    
          for (unsigned j = 0; j < cores.size(); ++j) 
            (*m_core_generalizers[i])(n, cores[j].first, cores[j].second, new_cores);
          cores.reset ();
          cores.append (new_cores);
        }
        
        for (unsigned i = 0; i < cores.size(); ++i) {
          expr_ref_vector const& core = cores[i].first;
          uses_level = cores[i].second;
          expr_ref lemma (m_pm.mk_not_and(core), m);
          TRACE("spacer", tout << "invariant state: " 
                << (is_infty_level(uses_level)?"(inductive)":"") 
                <<  mk_pp (lemma, m) << "\n";);
          n.pt().add_property (lemma, uses_level);
        }
        CASSERT("spacer", n.level() == 0 || check_invariant(n.level()-1));
        n.set_reachable (false);
        
        if (n.is_root ())
          n.set_reachable (false);
        // -- add parent as a leaf
        else
        {
          model_node &p = *n.parent ();
          p.reset_derivation ();
          m_search.enqueue_leaf (p);
          dealloc (&n);
        }
        break;
      }
        //something went wrong
      case l_undef: 
        TRACE("spacer", tout << "unknown state: " << mk_pp(m_pm.mk_and(cube), m) << "\n";);
        throw unknown_exception();
      }
      
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
    if (full_prop_lvl < max_prop_lvl) full_prop_lvl = max_prop_lvl;
    
    if (m_params.simplify_formulas_pre()) {
      simplify_formulas();
    }
    for (unsigned lvl = min_prop_lvl; lvl <= full_prop_lvl; lvl++) {
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
          pred_transformer& r = *it->m_value;
          r.propagate_to_infinity (lvl);
        }
        if (lvl <= max_prop_lvl)
        {
          m_inductive_lvl = lvl;
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
    if (m_params.simplify_formulas_post()) {            
      simplify_formulas();
    }
    return false;
  }

  void context::mk_reach_fact (model_node& n, model_evaluator &mev,
                               const datalog::rule& r, expr_ref& result, 
                               expr_ref_vector& child_reach_facts) {
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
            expr_ref o_ch_reach (m), n_ch_reach (m);
            ch_pt.get_used_origin_reach_fact (mev, i, n_ch_reach);
            m_pm.formula_n2o (n_ch_reach, o_ch_reach, i);
            path_cons.push_back (o_ch_reach);
            child_reach_facts.push_back (n_ch_reach);
            // collect o-vars to eliminate
            for (unsigned j = 0; j < pred->get_arity (); j++) {
                vars.push_back (m.mk_const (m_pm.o2o (ch_pt.sig (j), 0, i)));
            }
        }
        // collect aux vars to eliminate
        ptr_vector<app>& aux_vars = pt.get_aux_vars (r);
        vars.append (aux_vars.size (), aux_vars.c_ptr ());

        result = m_pm.mk_and (path_cons);

        TRACE ("spacer",
                tout << "Reach fact, before QE:\n";
                tout << mk_pp (result, m) << "\n";
                tout << "Vars:\n";
                for (unsigned i = 0; i < vars.size(); ++i) {
                    tout << mk_pp(vars.get (i), m) << "\n";
                }
              );

        qe_project (m, vars, result, mev.get_model ());

        TRACE ("spacer",
                tout << "Reach fact, after QE project:\n";
                tout << mk_pp (result, m) << "\n";
                tout << "Vars:\n";
                for (unsigned i = 0; i < vars.size(); ++i) {
                    tout << mk_pp(vars.get (i), m) << "\n";
                }
              );

        SASSERT (vars.empty ());

        m_stats.m_num_reach_queries++;
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
        qe_project (m, vars, phi1, mev.get_model ());
        qe::reduce_array_selects (*mev.get_model (), phi1);
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
        for (unsigned i = 0; i < preds.size (); ++i)
        {
          pred_transformer &pt = get_pred_transformer (preds [i]);
          deriv->add_premise (pt, i, 
                              pt.get_origin_summary (mev, prev_level (n.level ()),
                                                     i, reach_pred_used [i]),
                              reach_pred_used [i]);
        }
        n.set_derivation (deriv);

        // create post for the first child and add to queue
        model_node* ch = deriv->create_first_child (mev);
        SASSERT (ch);
        
        m_search.enqueue_leaf (*ch);
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

}
