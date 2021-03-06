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
        //m_reachable(pm, (datalog::SPACER_CACHE_MODE)ctx.get_params().cache_mode()),
        m_reach_case_assumps (m),
        _o_reach_case_assumps (m),
        m_mev (m)
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

    bool pred_transformer::is_reachable_known (expr* state, model_ref* M) {
        SASSERT (state);
        expr_ref assump (get_reach_facts_assump (), m);
        if (!assump) return false;
        m_reach_ctx->push ();
        m_reach_ctx->assert_expr (state);
        expr_ref_vector assumps (m);
        assumps.push_back (assump);
        lbool res = m_reach_ctx->check (assumps);
        if (M) m_reach_ctx->get_model (*M);
        m_reach_ctx->pop ();
        return (res == l_true);
    }

    /**
     * void pred_transformer::get_reach_explanation (model_ref const& M, expr_ref& reach_fact) {
     *     SASSERT (M);
     *     expr_ref bval (m);
     *     expr_ref_vector reach_facts (m);
     *     SASSERT (m_reach_case_assumps.size () == m_reach_facts.size ());
     *     for (unsigned i = 0; i < m_reach_case_assumps.size (); i++) {
     *         if (M->eval (m_reach_case_assumps.get (i), bval) && m.is_false (bval)) {
     *             reach_facts.push_back (m_reach_facts.get (i));
     *         }
     *     }
     *     reach_fact = m.mk_or (reach_facts.size (), reach_facts.c_ptr ());
     *     SASSERT (M->eval (reach_fact, bval) && m.is_true (bval));
     * }
     */

    void pred_transformer::get_used_reach_fact (model_ref& M, expr_ref& reach_fact) {
        expr_ref bval (m);
        for (unsigned i = 0; i < m_reach_case_assumps.size (); i++) {
            if (ctx.get_params ().use_heavy_mev ()) {
                m_mev.eval_heavy (M, m_reach_case_assumps.get (i), bval);
            }
            else {
                bval = m_mev.eval (M, m_reach_case_assumps.get (i));
            }
            if (m.is_false (bval)) {
                reach_fact = m_reach_facts.get (i);
                break;
            }
        }
        SASSERT (reach_fact);
    }

    void pred_transformer::get_used_o_reach_fact (model_ref& M, unsigned oidx, expr_ref& o_reach_fact, expr_ref& n_reach_fact) {
        expr_ref bval (m);
        for (unsigned i = 0; i < m_reach_case_assumps.size (); i++) {
            u_map<expr*> const& omap = m_o_reach_case_maps.get (i);
            expr* oassump;
            VERIFY (omap.find (oidx, oassump));
            if (ctx.get_params ().use_heavy_mev ()) {
                m_mev.eval_heavy (M, oassump, bval);
            }
            else {
                bval = m_mev.eval (M, oassump);
            }
            if (m.is_false (bval)) {
                n_reach_fact = m_reach_facts.get (i);
                pm.formula_n2o (n_reach_fact, o_reach_fact, oidx);
                break;
            }
        }
        SASSERT (o_reach_fact);
    }

    void pred_transformer::get_all_used_o_reach_facts (model_ref& M, unsigned oidx, expr_ref& reach_fact) {
        expr_ref bval (m);
        expr_ref_vector fmls (m);
        for (unsigned i = 0; i < m_reach_case_assumps.size (); i++) {
            u_map<expr*> const& omap = m_o_reach_case_maps.get (i);
            expr* oassump;
            VERIFY (omap.find (oidx, oassump));
            if (ctx.get_params ().use_heavy_mev ()) {
                m_mev.eval_heavy (M, oassump, bval);
            }
            else {
                bval = m_mev.eval (M, oassump);
            }
            if (m.is_false (bval)) {
                expr_ref fact (m);
                pm.formula_n2o (m_reach_facts.get (i), fact, oidx);
                fmls.push_back (fact);
            }
        }
        reach_fact = m.mk_or (fmls.size (), fmls.c_ptr ());
    }

    datalog::rule const* pred_transformer::get_just_rule (expr* fact) {
        reach_fact_just* j = m_reach_fact_justs.find (fact);
        TRACE ("spacer",
                tout << "justification: " << j << "\n";);
        //VERIFY (m_reach_fact_justs.find (fact, j));
        return &(j->r);
    }

    expr_ref_vector const* pred_transformer::get_just_pred_facts (expr* fact) {
        reach_fact_just* j = m_reach_fact_justs.find (fact);
        //VERIFY (m_reach_fact_justs.find (fact, j));
        return &(j->pred_reach_facts);
    }

    void pred_transformer::find_rules (model_core const& model, svector<datalog::rule const*>& rules) const {
        obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin(), end = m_tag2rule.end();
        TRACE("spacer_verbose",
              for (; it != end; ++it) {
                  expr* pred = it->m_key;
                  tout << mk_pp(pred, m) << ":\n";
                  if (it->m_value) it->m_value->display_smt2(m, tout) << "\n";                  
              }
        );
        
        it = m_tag2rule.begin();
        if (m_tag2rule.size() == 1) {
            rules.push_back (it->m_value);
            return;
        }

        expr_ref vl(m);
        unsigned cnt = 0;
        for (; it != end; ++it) {
            expr* pred = it->m_key;
            if (model.eval(to_app(pred)->get_decl(), vl) && m.is_true(vl)) {
                rules.push_back (it->m_value);
                cnt++;
            }
        }
        SASSERT (cnt > 0);
    }

    datalog::rule const* pred_transformer::find_rule(model& model, bool& is_concrete, vector<bool>& reach_pred_used, unsigned& num_reuse_reach) {
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
            expr* pred = it->m_key;
            if (model.eval(to_app(pred)->get_decl(), vl) && m.is_true(vl)) {
                r = it->m_value;
                is_concrete = true;
                num_reuse_reach = 0;
                reach_pred_used.reset ();
                unsigned tail_sz = r->get_uninterpreted_tail_size ();
                for (unsigned i = 0; i < tail_sz; i++) {
                    bool used = false;
                    func_decl* d = r->get_tail(i)->get_decl();
                    pred_transformer const& pt = ctx.get_pred_transformer (d);
                    expr_ref reach_assump (pt.get_o_reach_facts_assump (i), m);
                    if (!reach_assump) {
                        is_concrete = false;
                    }
                    else {
                        model_ref M (&model);
                        if (ctx.get_params ().use_heavy_mev ()) {
                            m_mev.eval_heavy (M, reach_assump, vl);
                        }
                        else {
                            vl = m_mev.eval (M, reach_assump);
                        }
                        if (m.is_true (vl)) used = true;
                        else is_concrete = false;
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
                TRACE("spacer", tout << "property1: " << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
                m_invariants.push_back(lemma);
                m_prop2level.insert(lemma, lvl);
                m_solver.add_formula(lemma);
                return true;
            }
            else {
                TRACE("spacer", tout << "already contained: " << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
                return false;
            }
        }
        ensure_level(lvl);        
        unsigned old_level;
        if (!m_prop2level.find(lemma, old_level) || old_level < lvl) {
            TRACE("spacer", tout << "property1: " << pp_level(lvl) << " " << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
            m_levels[lvl].push_back(lemma);
            m_prop2level.insert(lemma, lvl);
            m_solver.add_level_formula(lemma, lvl);
            return true;
        }
        else {
            TRACE("spacer", tout << "old-level: " << pp_level(old_level) << " " << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
            return false;
        }
    }

    void pred_transformer::add_child_property(pred_transformer& child, expr* lemma, unsigned lvl, bool is_reach_fact) {
        ensure_level(lvl);
        expr_ref_vector fmls(m);
        mk_assumptions(child.head(), lemma, fmls, is_reach_fact);
        for (unsigned i = 0; i < fmls.size(); ++i) {
            TRACE("spacer", tout << "child property: " << mk_pp(fmls[i].get(), m) << "\n";);
            if (is_infty_level(lvl)) {
                m_solver.add_formula(fmls[i].get());
            }
            else {
                m_solver.add_level_formula(fmls[i].get(), lvl);
            }
        }
    }

    void pred_transformer::add_property(expr* lemma, unsigned lvl) {
        expr_ref_vector lemmas(m);
        qe::flatten_and(lemma, lemmas);
        for (unsigned i = 0; i < lemmas.size(); ++i) {
            expr* lemma_i = lemmas[i].get();
            if (add_property1(lemma_i, lvl)) {
                IF_VERBOSE(2, verbose_stream() << pp_level(lvl) << " " << mk_pp(lemma_i, m) << "\n";);
                for (unsigned j = 0; j < m_use.size(); ++j) {
                    m_use[j]->add_child_property(*this, lemma_i, next_level(lvl));
                }
            }
        }
    }

    expr* pred_transformer::mk_fresh_reach_case_assump () const {
        std::stringstream name;
        name << head ()->get_name () << "#reach_case_" << m_reach_case_assumps.size ();
        return m.mk_fresh_const (name.str ().c_str (), m.mk_bool_sort());
    }

    expr* pred_transformer::get_reach_case_assump (unsigned idx) const {
        SASSERT (idx < m_reach_case_assumps.size ());
        return m_reach_case_assumps.get (idx);
    }

    expr* pred_transformer::mk_o_reach_case_assump (unsigned idx, unsigned oidx) {
        u_map<expr*>& omap = m_o_reach_case_maps.get (idx);
        expr* oassump;
        if (!omap.find (oidx, oassump)) {
            expr* assump = m_reach_case_assumps.get (idx);
            std::stringstream name;
            name << to_app (assump)->get_decl ()->get_name () << "#" << oidx;
            symbol sname (name.str ().c_str ());
            oassump = m.mk_const (sname, m.mk_bool_sort());
            _o_reach_case_assumps.push_back (oassump);
            omap.insert (oidx, oassump);
        }
        return oassump;
    }

    unsigned pred_transformer::get_num_reach_cases () const {
        return m_reach_case_assumps.size ();
    }

    void pred_transformer::add_reach_fact (expr* fact, datalog::rule const& r, expr_ref_vector const& child_reach_facts) {
        m_reach_facts.push_back (fact);
        reach_fact_just* j = alloc (reach_fact_just, r, child_reach_facts);
        m_reach_fact_justs.insert (fact, j);
        TRACE ("spacer",
                tout << "add_reach_fact: " << head()->get_name() << " " << mk_pp(fact, m) << "\n";);

        // update m_reach_ctx
        expr_ref new_case (m);
        new_case = mk_fresh_reach_case_assump ();
        expr_ref fml (m);
        if (m_reach_case_assumps.empty ()) {
            fml = m.mk_or (fact, new_case);
        } else {
            expr_ref last_case (m_reach_case_assumps.back (), m);
            fml = m.mk_or (m.mk_not (last_case), fact, new_case);
        }
        m_reach_case_assumps.push_back (new_case);
        m_o_reach_case_maps.push_back (u_map<expr*> ());
        m_reach_ctx->assert_expr (fml);
        TRACE ("spacer",
                tout << "updating reach ctx: " << mk_pp(fml, m) << "\n";);

        // update users; reach facts are independent of levels
        for (unsigned i = 0; i < m_use.size(); ++i) {
          m_use[i]->add_child_property (*this, fml, infty_level (), true);
        }
    }

    expr* pred_transformer::get_reach () {
        if (m_reach_facts.empty ()) {
            return m.mk_false ();
        }
        return m.mk_or (m_reach_facts.size (), m_reach_facts.c_ptr ());
    }

    expr* pred_transformer::get_reach_facts_assump () const {
        if (m_reach_case_assumps.empty ())
            return ((expr *)0);
        // return the negation of the last case
        return m.mk_not (m_reach_case_assumps.back ());
    }

    expr* pred_transformer::get_o_reach_facts_assump (unsigned oidx) const {
        if (m_reach_case_assumps.empty ())
            return ((expr *)0);
        // return the negation of the last case
        u_map<expr*> const& omap = m_o_reach_case_maps.back ();
        SASSERT (omap.contains (oidx));
        return m.mk_not (omap.find (oidx));
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

    void pred_transformer::add_o_lemmas (int level, int oidx, expr_ref_vector& forms) const {
        SASSERT (level >= -1);
        SASSERT (oidx >= 0);

        expr_ref_vector::iterator it;
        expr_ref lem_o (m);

        // add invariants
        for (it = m_invariants.begin (); it != m_invariants.end (); it++) {
            pm.formula_n2o (*it, lem_o, oidx);
            forms.push_back (lem_o);
            TRACE ("spacer", tout << "Invariant: " << mk_pp (lem_o, m) << "\n";);
        }

        if (level == -1) return;

        // add level lemmas
        for (unsigned l = (unsigned)level; l < m_levels.size (); l++) {
            for (it = m_levels[l].begin (); it != m_levels[l].end (); it++) {
                pm.formula_n2o (*it, lem_o, oidx);
                forms.push_back (lem_o);
                TRACE ("spacer", tout << "Lemma: " << mk_pp (lem_o, m) << "\n";);
            }
        }
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
      
        if (m_levels.empty ()) return;

        for (unsigned i = m_levels.size (); i > level; --i)
        {
          expr_ref_vector &lemmas = m_levels [i-1];
          for (unsigned j = 0; j < lemmas.size (); ++j)
            add_property(lemmas[j].get (), infty_level ());
          lemmas.reset();
        }
    }

    bool pred_transformer::is_reachable_with_reach_facts (model_node& n, datalog::rule const& r) {
        expr_ref_vector assumps (m);
        assumps.push_back (n.post ());

        TRACE ("spacer",
                tout << "post query:\n";
                tout << mk_pp (n.post (), m) << "\n";
              );

        expr* r_tag = rule2tag (&r);
        assumps.push_back (r_tag);

        TRACE ("spacer",
                tout << "rule tag: " << mk_pp (r_tag, m) << "\n";
              );

        find_predecessors(r, m_predicates);

        TRACE ("spacer",
                tout << "num preds: " << m_predicates.size () << "\n";
              );

        for (unsigned i = 0; i < m_predicates.size(); i++) {
            func_decl* d = m_predicates[i];
            pred_transformer const& pt = ctx.get_pred_transformer (d);
            expr_ref assump (pt.get_o_reach_facts_assump (i), m);
            VERIFY (assump);
            assumps.push_back (assump);

            TRACE ("spacer",
                    tout << "reach assumption: " << mk_pp (assump, m) << "\n";
                  );
        }

        // disable all level lemmas
        prop_solver::scoped_level _sl(m_solver, infty_level());
        expr_ref_vector core (m);
        m_solver.set_core (&core);
        model_ref model;
        m_solver.set_model(&model);
        expr_ref_vector aux (m);
        lbool is_sat = m_solver.check_assumptions (assumps, aux);
        core.reset();
        if (is_sat == l_true) {            
            TRACE ("spacer", tout << "reachable using reach facts\n"; 
                    model_smt2_pp (tout, m, *model, 0);
                  );
            ctx.set_curr_model (model);
            return true;
        }
        return false;
    }

    lbool pred_transformer::is_reachable(model_node& n, expr_ref_vector* core, unsigned& uses_level, 
                                         bool& is_concrete, datalog::rule const*& r, vector<bool>& reach_pred_used, unsigned& num_reuse_reach) {
        TRACE("spacer", 
              tout << "is-reachable: " << head()->get_name() << " level: " << n.level() << "\n";
              tout << mk_pp(n.post(), m) << "\n";);

        ensure_level(n.level());        

        // prepare the solver
        model_ref model;
        prop_solver::scoped_level _sl(m_solver, n.level());
        m_solver.set_core(core);
        m_solver.set_model(&model);

        expr_ref_vector post (m), reach_assumps (m);
        post.push_back (n.post ());

        // populate reach_assumps
        if (ctx.get_params ().eager_reach_check () && n.level () > 0 && !m_all_init) {
            obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin (),
                end = m_tag2rule.end ();
            for (; it != end; ++it) {
                datalog::rule const* r = it->m_value;
                if (!r) continue;
                find_predecessors(*r, m_predicates);
                if (m_predicates.empty ()) continue;
                for (unsigned i = 0; i < m_predicates.size(); i++) {
                    func_decl* d = m_predicates[i];
                    pred_transformer const& pt = ctx.get_pred_transformer (d);
                    expr_ref assump (pt.get_o_reach_facts_assump (i), m);
                    if (assump) {
                        reach_assumps.push_back (assump);
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
            ctx.set_curr_model (model);

            TRACE ("spacer", tout << "reachable\n";);

            r = find_rule (*model, is_concrete, reach_pred_used, num_reuse_reach);
            // populate reach_pred_used
            /**
             * find_predecessors(*r, m_predicates);
             * ast_eq_proc eq_proc;
             * for (unsigned i = 0; i < m_predicates.size(); i++) {
             *     func_decl* d = m_predicates[i];
             *     pred_transformer const& pt = ctx.get_pred_transformer (d);
             *     bool reach_used = false;
             *     expr_ref assump (pt.get_o_reach_facts_assump (i), m);
             *     if (assump) {
             *         for (unsigned j = 0; j < reach_assumps.size (); j++) {
             *             if (eq_proc (assump, reach_assumps.get (j))) {
             *                 reach_used = true;
             *                 break;
             *             }
             *         }
             *     }
             *     reach_pred_used.push_back (reach_used);
             * }
             */

            return l_true;
        }
        if (is_sat == l_false) {
            SASSERT (reach_assumps.empty ());
            TRACE ("spacer", tout << "unreachable with lemmas\n";);
            TRACE ("spacer",
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
        manager& pm = get_spacer_manager();
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

    void pred_transformer::mk_assumptions(func_decl* head, expr* fml, expr_ref_vector& result, bool is_reach_fact) {
        expr_ref tmp1(m), tmp2(m);
        expr_substitution sub (m);
        proof_ref pr (m.mk_asserted (m.mk_true ()), m);
        obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin(), end = m_tag2rule.end();
        for (; it != end; ++it) {
            expr* pred = it->m_key;
            datalog::rule const* r = it->m_value;
            if (!r) continue;
            find_predecessors(*r, m_predicates);
            for (unsigned i = 0; i < m_predicates.size(); i++) {
                func_decl* d = m_predicates[i];
                if (d == head) {
                    tmp1 = m.mk_implies(pred, fml);
                    pm.formula_n2o(tmp1, tmp2, i);

                    if (is_reach_fact) {
                        // replace reach case assumps with o-versions;
                        // only need to care about the last two assumps
                        pred_transformer& pt = ctx.get_pred_transformer (head);
                        unsigned num_cases = pt.get_num_reach_cases ();
                        sub.reset ();
                        expr_ref case1 (m), case2 (m);
                        expr_ref ocase1 (m), ocase2 (m);

                        case1 = pt.get_reach_case_assump (num_cases-1);
                        ocase1 = pt.mk_o_reach_case_assump (num_cases-1, i);
                        sub.insert (case1, ocase1, pr);
                        if (num_cases > 1) {
                            case2 = pt.get_reach_case_assump (num_cases-2);
                            ocase2 = pt.mk_o_reach_case_assump (num_cases-2, i);
                            sub.insert (case2, ocase2, pr);
                        }

                        scoped_ptr<expr_replacer> rep = mk_default_expr_replacer (m);
                        rep->set_substitution (&sub);
                        (*rep) (tmp2);
                    }

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
    // model_node

    //static bool is_ini(datalog::rule const& r) {
        //return r.get_uninterpreted_tail_size() == 0;
    //}

    //unsigned model_node::m_count;

    void model_node::close () {
        m_open = false;
        del_derivs ();
        if (is_inq ()) m_search.erase_leaf (*this);
    }

    void model_node::del_derivs () {
        // deallocate every deriv
        for (ptr_vector<derivation>::iterator it = m_derivs.begin ();
                it != m_derivs.end (); it++) {
            dealloc (*it);
        }
        // empty the vector
        m_derivs.reset ();
    }

    void model_node::del_derivs (pred_transformer const& pt, unsigned level) {
        ptr_vector<derivation>::iterator it = m_derivs.begin ();
        while (it != m_derivs.end ()) {
            TRACE ("spacer", tout << (*it) << "\n";);
            if ((*it)->has_prem (pt, level)) {
                TRACE ("spacer", tout << "Deleting " << (*it) << "\n";);
                dealloc (*it);
                m_derivs.erase (it);
            } else it++;
        }
    }

    void model_node::del_derivs (derivation* d) {
        m_derivs.erase (d);
        dealloc (d);
    }

    void model_node::del_derivs_except (derivation* d) {
        SASSERT (d);
        // deallocate every deriv except d
        for (ptr_vector<derivation>::iterator it = m_derivs.begin ();
                it != m_derivs.end (); it++) {
            if ((*it) != d) dealloc (*it);
        }
        // empty the vector and add d
        m_derivs.reset ();
        add_deriv (d);
    }

    bool model_node::has_derivs (unsigned level) const {
        for (ptr_vector<derivation>::const_iterator it = m_derivs.begin ();
                it != m_derivs.end (); it++) {
            if ((*it)->curr ().level () == level) return true;
        }
        return false;
    }

    model_node::~model_node () {
        TRACE ("spacer",
                tout << "Deleting model node:" << this << "\n";
              );
        if (is_inq ()) m_search.erase_leaf (*this);
        del_derivs ();
    }

/*
    datalog::rule* model_node::get_rule() {
        if (m_rule) {
            return const_cast<datalog::rule*>(m_rule);
        }
        // only initial states are not set by the SPACER search.
        datalog::rule const& rl1 = pt().find_rule(*m_model);
        if (is_ini(rl1)) {
            set_rule(&rl1);
            return const_cast<datalog::rule*>(m_rule);
        }
        ast_manager& m = pt().get_manager();
        // otherwise, the initial state is reachable.
        ptr_vector<datalog::rule> const& rules = pt().rules();
        ptr_vector<datalog::rule> ini_rules;
        expr_ref_vector tags(m);
        expr_ref ini_tags(m), ini_state(m);
        for (unsigned i = 0; i < rules.size(); ++i) {
            datalog::rule* rl = rules[i];
            if (is_ini(*rl)) {
                tags.push_back(pt().rule2tag(rl));
            }
        }
        SASSERT(!tags.empty());
        ini_tags = m.mk_or(tags.size(), tags.c_ptr());
        ini_state = m.mk_and(ini_tags, pt().initial_state(), state());
        model_ref mdl;
        pt().get_solver().set_model(&mdl);
        VERIFY(l_true == pt().get_solver().check_conjunction_as_assumptions(ini_state));
        datalog::rule const& rl2 = pt().find_rule(*mdl);
        SASSERT(is_ini(rl2));
        set_rule(&rl2);
        return const_cast<datalog::rule*>(m_rule);
    }

    void model_node::mk_instantiate(datalog::rule_ref& r0, datalog::rule_ref& r1, expr_ref_vector& binding) {
        ast_manager& m = pt().get_manager();
        expr_ref_vector conjs(m);
        obj_map<expr,expr*> model;
        qe::flatten_and(state(), conjs);
        for (unsigned i = 0; i < conjs.size(); ++i) {
            expr* e = conjs[i].get(), *e1, *e2;
            if (m.is_eq(e, e1, e2) || m.is_iff(e, e1, e2)) {
                if (m.is_value(e2)) {
                    model.insert(e1, e2);
                }
                else if (m.is_value(e1)) {
                    model.insert(e2, e1);
                }
            }
            else if (m.is_not(e, e1)) {
                model.insert(e1, m.mk_false());
            }
            else {
                model.insert(e, m.mk_true());
            }
        }
        r0 = get_rule();
        app_ref_vector& inst = pt().get_inst(r0);
        TRACE("spacer", tout << mk_pp(state(), m) << " instance: " << inst.size() << "\n";);
        for (unsigned i = 0; i < inst.size(); ++i) {
            expr* v;
            if (model.find(inst[i].get(), v)) {
                binding.push_back(v);
            }            
            else {
                binding.push_back(m.mk_var(i, m.get_sort(inst[i].get())));
            }            
        }
        r1 = r0;
        if (!inst.empty()) {
            r1.get_manager().substitute(r1, binding.size(), binding.c_ptr());
        }
    }


    std::ostream& model_node::display(std::ostream& out, unsigned indent) {
        for (unsigned i = 0; i < indent; ++i) out << " ";
        out << m_level << " " << m_pt.head()->get_name() << " " << (m_closed?"closed":"open") << "\n";
        for (unsigned i = 0; i < indent; ++i) out << " ";
        out << "  " << mk_pp(m_state, m_state.get_manager(), indent) << "\n";
        for (unsigned i = 0; i < children().size(); ++i) {
            children()[i]->display(out, indent + 1);
        }
        return out;
    }

    unsigned model_node::index() const {
        model_node* p = parent();
        if (!p) return 0;
        for (unsigned i = 0; i < p->children().size(); ++i) {
            if (this == p->children()[i]) return i;
        }
        UNREACHABLE();
        return 0;
    }

*/

    // ----------------
    // derivation

    derivation::derivation (model_node* concl,
                            ptr_vector<pred_transformer>& pred_pts,
                            vector<bool> const& reach_pred_used,
                            vector<unsigned> pred_o_idx,
                            datalog::rule const& rule,
                            model_search& search,
                            context const& ctx):
        m_concl (concl),
        m_reach_pred_used (reach_pred_used),
        m_o_idx (pred_o_idx),
        m_rule (rule),
        m_curr_it (0),
        m (m_concl->get_manager ()),
        m_sm (m_concl->get_spacer_manager ()),
        m_ctx (ctx),
        m_trans (m),
        m_prem_facts (m),
        M (0)
    {
        SASSERT (m_concl); // non-null
        for (unsigned i = 0; i < pred_pts.size (); i++) {
            pred_transformer& pt = *(pred_pts [i]);
            // create model node for the premise
            m_prems.push_back (alloc (model_node, m_concl, pt, m_concl->level()-1, this, search));
            // populate n-vars and o-vars of pt
            m_ovars.push_back (app_ref_vector (m));
            m_nvars.push_back (app_ref_vector (m));
            app_ref_vector& pt_ovars = m_ovars.back ();
            app_ref_vector& pt_nvars = m_nvars.back ();
            unsigned sig_size = pt.head()->get_arity();
            for (unsigned j = 0; j < sig_size; ++j) {
                pt_ovars.push_back (m.mk_const (m_sm.o2o (pt.sig (j), 0, m_o_idx [i])));
                pt_nvars.push_back (m.mk_const (m_sm.o2n (pt.sig (j), 0)));
            }
        }
        // initialize m_curr_it to point to nothing
        m_curr_it = m_prems.end ();
    }

    /**
     * traverse e to make ghosts for the uninterpreted leaves;
     * for now, does not handle quantifiers and de-bruijn variables
     */
    /*void derivation::mk_ghosts (ast_mark& mark, ptr_vector<expr>& todo, expr* e) {
        todo.push_back(e);
        while (!todo.empty()) {
            e = todo.back();
            todo.pop_back();
            if (mark.is_marked(e)) {
                continue;
            }
            mark.mark(e, true);
            switch(e->get_kind()) {
            case AST_QUANTIFIER: {
                // not handling quantifiers for now
                UNREACHABLE();
                break;
            }
            case AST_VAR: {
                // not handling variables for now;
                UNREACHABLE();
                break;
            }
            case AST_APP: {
                app* a = to_app(e);
                if (is_uninterp_const (a) && !model_node::is_ghost (a->get_decl ())) {
                    unsigned idx; // store in this, the o-index of a
                    m_sm.get_o_index (a->get_decl (), idx);
                    SASSERT (m_ghosts.size () > idx); // m_ghosts is expected to be of the right size
                    app* ghost = m_concl->mk_ghost (a);
                    app_ref_vector vec (m);
                    vec.push_back (a);
                    vec.push_back (ghost);
                    m_ghosts[idx].push_back (vec);
                    TRACE ("spacer", tout << "Orig: " << mk_pp (a, m) << "\n";);
                    TRACE ("spacer", tout << "Ghost: " << mk_pp (ghost, m) << "\n";);
                    TRACE ("spacer", tout << "o-index: " << idx << "\n";);
                } else {
                    for (unsigned i = 0; i < a->get_num_args(); ++i) {
                        todo.push_back(a->get_arg(i));
                    }
                }
                break;
            }
            default:
                UNREACHABLE();
            }
        }
    }

    void derivation::mk_ghosts (expr_ref const& phi) {
        m_ghosts.reset ();
        m_ghosts.resize (num_prems (), vector<app_ref_vector>());
        ast_mark mark;
        ptr_vector<expr> todo;
        mk_ghosts (mark, todo, phi.get ());
    }

    void derivation::mk_ghost_sub (expr_substitution& sub) const {
        sub.reset ();
        for (vector<vector<app_ref_vector> >::const_iterator it = m_ghosts.begin ();
                it != m_ghosts.end (); it++) {
            if ((*it).empty ()) continue; // no ghosts for this idx
            for (vector<app_ref_vector>::const_iterator g_it = it->begin ();
                    g_it != it->end (); g_it++) {
                app_ref_vector const& vec = *g_it;
                SASSERT (vec.size () == 2); // it's a pair
                sub.insert (vec[0], vec[1]);
            }
        }
    }

    void derivation::mk_unghost_sub (expr_substitution& sub) const {
        sub.reset ();
        SASSERT (m_curr_it != m_prems.end ()); // points to something
        vector<app_ref_vector> const& curr_ghosts = m_ghosts[curr_o_idx ()];
        if (curr_ghosts.empty ()) return; // no ghosts for curr_o_idx ()
        for (vector<app_ref_vector>::const_iterator g_it = curr_ghosts.begin ();
                g_it != curr_ghosts.end (); g_it++) {
            app_ref_vector const& vec = *g_it;
            app* orig_o = vec[0];
            app* ghost = vec[1];
            app* orig_n = m.mk_const (m_sm.o2n (orig_o->get_decl (), curr_o_idx ()));
            sub.insert (ghost, orig_n);
        }
    }

    void derivation::ghostify (expr_ref& phi) {
        mk_ghosts (phi);
        TRACE ("spacer", tout << "before ghostify: " << mk_pp(phi,m) << "\n";);
        expr_substitution sub (m);
        mk_ghost_sub (sub);
        scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer (m);
        rep->set_substitution (&sub);
        (*rep) (phi);
        TRACE ("spacer", tout << "after ghostify: " << mk_pp(phi,m) << "\n";);
    }*/

    void derivation::setup (expr_ref& phi, model_ref& mdl) {
        m_trans = phi;
        M = mdl;

        // update m_prem_facts with (implicants of) reach-facts/lemmas according to m_reach_pred_used
        m_prem_facts.reset ();
        for (unsigned i = 0; i < m_prems.size (); i++) {
            pred_transformer& pt = m_prems[i]->pt ();
            expr_ref_vector facts (m);
            if (m_reach_pred_used.get (i)) {
                expr_ref reach_fact (m);
                expr_ref _n_reach_fact (m);
                pt.get_used_o_reach_fact (M, m_o_idx[i], reach_fact, _n_reach_fact);
                TRACE ("spacer",
                        tout << "setup reach fact:" << mk_pp (reach_fact, m) << "\n";
                      );
                facts.push_back (reach_fact);
            }
            else {
                pt.add_o_lemmas (m_concl->level ()-1, m_o_idx[i], facts);
            }
            // get an implicant
            qe::flatten_and (facts);
            ptr_vector<expr> facts1 (facts.size (), facts.c_ptr ());
            model_evaluator mev (m);
            expr_ref_vector lits (m);
            mev.minimize_literals (facts1, M, lits);
            m_prem_facts.push_back (m_sm.mk_and (lits));
            TRACE ("spacer",
                    if (m_reach_pred_used.get (i)) {
                        tout << "setup added fact:" << mk_pp (m_prem_facts.back (), m) << "\n";
                    }
                  );
        }
    }

    /*void derivation::mk_prem_post (expr_ref& phi, expr_ref& ctx) const {
        TRACE ("spacer", tout << "input to post: " << mk_pp(phi,m) << "\n";);
        expr_substitution sub (m);
        mk_unghost_sub (sub);
        scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer (m);
        rep->set_substitution (&sub);
        (*rep) (phi);
        ctx = expr_ref (m.mk_true (), m);
        TRACE ("spacer", tout << "output of post: " << mk_pp(phi,m) << "\n";);
    }*/

    void derivation::updt_setup () {
        SASSERT (m_curr_it != m_prems.end ());

        expr_ref_vector fmls (m);
        pred_transformer& pt = curr ().pt ();

        // get new model consistent with m_trans, new reach fact of current
        // child and facts of remaining children
        expr_ref n_trans (m);
        m_sm.formula_o2n (m_trans, n_trans, curr_o_idx (), false);
        fmls.push_back (n_trans);
        TRACE ("spacer",
                tout << "ntrans: " << mk_pp (n_trans, m) << "\n";
              );
        for (unsigned i = curr_idx ()+1; i < m_prems.size (); i++) {
            fmls.push_back (m_prem_facts.get (i));
            TRACE ("spacer",
                    tout << "prem fact: " << mk_pp (m_prem_facts.get (i), m) << "\n";
                    tout << "prem is reach: " << m_reach_pred_used.get (i) << "\n";
                  );
        }
        VERIFY (pt.is_reachable_known (m_sm.mk_and (fmls), &M));

        // get new reach fact
        expr_ref reach_fact (m);
        //if (m_ctx.get_params ().eager_reach_check ()) {
            //reach_fact = pt.get_last_reach_fact ();
        //}
        //else {
            pt.get_used_reach_fact (M, reach_fact);
        //}
        TRACE ("spacer",
                tout << "Post of derivation with n-vars for current index:\n"
                << mk_pp (m_trans, m) << "\n";
                tout << "Using reach fact of " << curr ().pt ().head ()->get_name () << ":\n"
                << mk_pp (reach_fact, m) << "\n";
                tout << "Model:\n";
                model_smt2_pp (tout, m, *M, 0);
              );

        // pick an implicant
        expr_ref_vector facts (m);
        facts.push_back (reach_fact);
        qe::flatten_and (facts);
        ptr_vector<expr> facts1 (facts.size (), facts.c_ptr ());
        model_evaluator mev (m);
        expr_ref_vector lits (m);
        mev.minimize_literals (facts1, M, lits);
        expr_ref impl (m_sm.mk_and (lits), m);

        // update m_prem_facts
        expr_ref oimpl (m);
        m_sm.formula_n2o (impl, oimpl, curr_o_idx ());
        m_prem_facts.set (curr_idx (), oimpl);

        // update m_trans
        fmls.reset ();
        fmls.push_back (n_trans);
        fmls.push_back (impl);
        m_trans = m_sm.mk_and (fmls);
        qe_project (m, m_nvars [curr_idx ()], m_trans, M, true);
    }

    model_node* derivation::mk_next () {
        expr_ref_vector jump_facts (m);
        app_ref_vector vars (m);
        model_node* sib;

        /**
         * // populate reach facts to jump over
         * if (m_curr_it != m_prems.end ()) {
         *     // M is over n-vars of curr child
         *     expr_ref n_reach_fact (m);
         *     m_sm.formula_o2n (m_prem_facts.get (curr_idx ()), n_reach_fact, curr_o_idx ());
         *     jump_facts.push_back (n_reach_fact);
         *     vars.append (m_nvars [curr_idx ()]);
         *     m_sm.formula_o2n (m_trans, m_trans, curr_o_idx (), false);
         * }
         */
        bool no_next = true;
        while (has_next ()) {
            sib = next (); // updates m_curr_it
            if (!m_reach_pred_used.get (curr_idx ())) {
                no_next = false;
                break;
            }
            jump_facts.push_back (m_prem_facts.get (curr_idx ()));
            vars.append (m_ovars [curr_idx ()]);
        }

        if (no_next) { // no more children to process
            return (model_node*) (0);
        }

        // update m_trans
        jump_facts.push_back (m_trans);
        m_trans = m_sm.mk_and (jump_facts);
        if (!vars.empty ()) {
            qe_project (m, vars, m_trans, M, true);
            TRACE ("spacer",
                    tout << "Updated post of derivation:\n"
                         << mk_pp (m_trans, m) << "\n";
                  );
        }

        // create post for sib; use all prem facts except the current
        vars.reset ();
        expr_ref_vector fmls (m);
        fmls.push_back (m_trans);
        for (unsigned i = curr_idx ()+1; i < m_prems.size (); i++) {
            fmls.push_back (m_prem_facts.get (i));
            vars.append (m_ovars [i]);
        }
        expr_ref sib_post (m_sm.mk_and (fmls), m);
        qe_project (m, vars, sib_post, M, true);
        m_sm.formula_o2n (sib_post, sib_post, curr_o_idx ());

        // update sib
        sib->reset ();
        sib->updt_post (sib_post);
        TRACE ("spacer",
                tout << "Post of next sibling:\n"
                << mk_pp (sib_post, m) << "\n";
              );
        return sib;

/**
 *         if (m_curr_it != m_prems.end ()) {
 *             // project vars of current pt and update m_post
 *             idx = (m_curr_it - m_prems.begin ());
 *             vars.append (m_nvars[idx]);
 *             qe_project (m, vars, m_post, M);
 *             TRACE ("spacer",
 *                     tout << "Updated post of derivation:\n"
 *                          << mk_pp (m_post, m) << "\n";
 *                   );
 *             idx += 2;
 *         }
 * 
 *         // project all variables except those of the next premise
 *         for (; idx < m_prems.size (); idx++) {
 *             vars.append (m_ovars[idx]);
 *         }
 *         expr_ref post_actual (m);
 *         post_actual = m_post;
 *         qe_project (m, vars, post_actual, M);
 * 
 *         // next sibling; this updates local bookkeeping info about o-indices, etc.
 *         model_node& sib = next ();
 *         sib.reset ();
 * 
 *         TRACE ("spacer",
 *                 tout << "post on actual params:\n"
 *                      << mk_pp (post_actual, m) << "\n";
 *                 tout << "o-idx: " << curr_o_idx () << "\n";
 *               );
 * 
 *         // replace actuals by formals
 *         m_sm.formula_o2n (post_actual, post, curr_o_idx ());
 *         TRACE ("spacer",
 *                 tout << "Post of next sibling:\n"
 *                 << mk_pp (post, m) << "\n";
 *               );
 * 
 *         return sib;
 */
    }

    /*void derivation::get_trace (expr_ref_vector& trace_conjs) const {
        expr_substitution sub (m);
        expr* c1;
        expr* c2;
        // obtain traces of m_prems in reverse order
        if (m_prems.size () > 0) {
            for (unsigned i = 0; i < m_prems.size (); i++) {
                unsigned idx = m_prems.size ()-i-1;
                model_node* prem = m_prems [idx];
                SASSERT (prem->closing_deriv ());
                prem->closing_deriv ()->get_trace (trace_conjs);
                // version all the o-consts
                pred_transformer const& pt = prem->pt ();
                unsigned sig_size = pt.sig_size ();
                for (unsigned j = 0; j < sig_size; j++) {
                    c1 = m.mk_const (m_sm.o2o (pt.sig (j), 0, m_o_idx [idx]));
                    c2 = m.mk_const (m_sm.o2o (pt.sig (j), 0, prem->id ()));
                    sub.insert (c1, c2);
                }
            }
        }
        // version n-consts and the auxiliaries
        pred_transformer& concl_pt = m_concl->pt ();
        unsigned sig_size = concl_pt.sig_size ();
        for (unsigned j = 0; j < sig_size; j++) {
            c1 = m.mk_const (m_sm.o2n (concl_pt.sig (j), 0));
            c2 = m.mk_const (m_sm.o2o (concl_pt.sig (j), 0, m_concl->id ()));
            sub.insert (c1, c2);
        }
        ptr_vector<app>& aux_vars = concl_pt.get_aux_vars (m_rule);
        for (unsigned j = 0; j < aux_vars.size (); j++) {
            app* var = aux_vars [j];
            sort* s = var->get_decl ()->get_range ();
            std::stringstream new_name;
            new_name << var->get_decl ()->get_name () << "_" << m_concl->id ();
            app* new_var = m.mk_const (symbol (new_name.str ().c_str ()), s);
            sub.insert (var, new_var);
        }

        scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
        rep->set_substitution(&sub);

        // add transition relation
        expr* T = concl_pt.get_transition (m_rule);
        expr_ref T_v (m);
        (*rep) (T, T_v);
        trace_conjs.push_back (T_v);
    }*/

    derivation::~derivation () {
        TRACE ("spacer",
                tout << "Destroying deriv:" << this << "\n";
              );
        // destroy m_prems
        while (!m_prems.empty ()) {
            model_node* n = m_prems.back ();
            m_prems.pop_back ();
            dealloc (n);
        }
    }

    // ----------------
    // model_search

    model_node* model_search::next () {
        if (m_leaves.empty ()) {
            return 0;
        }
        model_node* result = m_leaves.top ();
        m_leaves.pop ();
        result->outq ();
        TRACE ("spacer",
                tout << "Popping node for PT:" << result->pt().head()->get_name()
                     << " " << result
                     << " at level:" << result->level() << "\n";
              );
        return result;
    }

/*
    bool model_search::is_repeated(model_node& n) const {
        model_node* p = n.parent();
        while (p) {
            if (p->post() == n.post()) {
                return true;
            }
            p = p->parent();
        }
        return false;
    }
*/

    void model_search::add_leaf(model_node& n) {
        set_leaf (n);
        /*unsigned& count = cache(n).insert_if_not_there2(n.post(), 0)->get_data().m_value;
        ++count;
        if (count == 1 || is_repeated(n)) {
            set_leaf(n);
        }
        else {
            n.set_pre_closed();
        }*/
    }

    void model_search::set_leaf(model_node& n) {
        enqueue_leaf(n);
    }

    void model_search::enqueue_leaf(model_node& n) {
        m_leaves.push (&n);
        n.inq ();
        TRACE ("spacer",
                tout << "Enqueuing node for PT:" << n.pt().head()->get_name()
                     << " " << &n
                     << " at level:" << n.level() << "\n";
              );
    }

    void model_search::set_root(model_node* root) {
        reset();
        m_root = root;
        //SASSERT(cache(*root).empty());        
        //cache(*root).insert(root->post(), 1);
        set_leaf(*root);
    }

    void model_search::erase_leaf (model_node& n) { m_leaves.erase (&n); n.outq ();
        TRACE ("spacer",
                tout << "Erasing node for PT:" << n.pt().head()->get_name()
                     << " " << &n
                     << " at level:" << n.level() << "\n";
              );
    }


/*    obj_map<expr, unsigned>& model_search::cache(model_node const& n) {
        unsigned l = n.orig_level();
        if (l >= m_cache.size()) {
            m_cache.resize(l + 1);
        }
        return m_cache[l];
    }

    std::ostream& model_search::display(std::ostream& out) const {
        if (m_root) {
            m_root->display(out, 0);
        }
        out << "goals\n";
        std::deque<model_node*>::const_iterator 
            it  = m_leaves.begin(), 
            end = m_leaves.end();
        for (; it != end; ++it) {
            (*it)->display(out, 1);
        }
        return out;
    }
*/


    /**
       \brief Ensure that all nodes in the tree have associated models.
       get_trace and get_proof_trace rely on models to extract rules.
     */

/*
    void model_search::update_models() {
        obj_map<expr, model*> models;
        ptr_vector<model_node> todo;
        todo.push_back(m_root);
        while (!todo.empty()) {
            model_node* n = todo.back();
            if (n->get_model_ptr()) {
                models.insert(n->state(), n->get_model_ptr());
            }
            todo.pop_back();
            todo.append(n->children().size(), n->children().c_ptr());
        }

        todo.push_back(m_root);
        while (!todo.empty()) {
            model_node* n = todo.back();
            model* md = 0;
            if (!n->get_model_ptr() && models.find(n->state(), md)) {
                model_ref mr(md);
                n->set_model(mr);
            }
            todo.pop_back();
            todo.append(n->children().size(), n->children().c_ptr());
        }        
    }
*/

    /**
       Extract trace comprising of constraints 
       and predicates that are satisfied from facts to the query.
       The resulting trace 
     */
    expr_ref model_search::get_trace(context const& ctx) {
        ast_manager& m = ctx.get_manager ();
        return expr_ref (m.mk_true (), m);
        /*SASSERT (m_root->closing_deriv ());
        expr_ref_vector trace_conjs (m);
        m_root->closing_deriv ()->get_trace (trace_conjs);
        TRACE ("spacer",
                tout << "Trace:" << "\n";
                tout << mk_pp (m.mk_and (trace_conjs.size (), trace_conjs.c_ptr ()), m) << "\n";
              );
        expr_ref result (m.mk_and (trace_conjs.size (), trace_conjs.c_ptr ()), m);
        return result;*/
    }
/*
    expr_ref model_search::get_trace(context const& ctx) {       
        pred_transformer& pt = get_root().pt();
        ast_manager& m = pt.get_manager();
        manager& pm = pt.get_spacer_manager();
        datalog::context& dctx = ctx.get_context();
        datalog::rule_manager& rm = dctx.get_rule_manager();
        expr_ref_vector constraints(m), predicates(m);
        expr_ref tmp(m);
        ptr_vector<model_node> children;
        unsigned deltas[2];
        datalog::rule_ref rule(rm), r0(rm);
        model_node* n = m_root;
        datalog::rule_counter& vc = rm.get_counter();
        substitution subst(m);
        unifier unif(m);
        rule = n->get_rule();
        unsigned max_var = vc.get_max_rule_var(*rule);
        predicates.push_back(rule->get_head());
        children.push_back(n);
        bool first = true;
        update_models();
        while (!children.empty()) {
            SASSERT(children.size() == predicates.size());
            expr_ref_vector binding(m);
            n = children.back();
            children.pop_back();
            TRACE("spacer", n->display(tout, 0););
            n->mk_instantiate(r0, rule, binding);
            
            max_var = std::max(max_var, vc.get_max_rule_var(*rule));
            subst.reset();
            subst.reserve(2, max_var+1);
            deltas[0] = 0;
            deltas[1] = max_var+1;
        
            VERIFY(unif(predicates.back(), rule->get_head(), subst));
            for (unsigned i = 0; i < constraints.size(); ++i) {
                subst.apply(2, deltas, expr_offset(constraints[i].get(), 0), tmp);
                dctx.get_rewriter()(tmp);
                constraints[i] = tmp;
            }
            for (unsigned i = 0; i < predicates.size(); ++i) {
                subst.apply(2, deltas, expr_offset(predicates[i].get(), 0), tmp);
                predicates[i] = tmp;
            }
            if (!first) {
                constraints.push_back(predicates.back());
            }
            first = false;
            predicates.pop_back();
            for (unsigned i = 0; i < rule->get_uninterpreted_tail_size(); ++i) {
                subst.apply(2, deltas, expr_offset(rule->get_tail(i), 1), tmp);
                predicates.push_back(tmp);
            }
            for (unsigned i = rule->get_uninterpreted_tail_size(); i < rule->get_tail_size(); ++i) {
                subst.apply(2, deltas, expr_offset(rule->get_tail(i), 1), tmp);
                dctx.get_rewriter()(tmp);
                if (!m.is_true(tmp)) {
                    constraints.push_back(tmp);
                }
            }
            for (unsigned i = 0; i < constraints.size(); ++i) {
                max_var = std::max(vc.get_max_var(constraints[i].get()), max_var);
            }
            for (unsigned i = 0; i < predicates.size(); ++i) {
                max_var = std::max(vc.get_max_var(predicates[i].get()), max_var);
            }
            children.append(n->children());
        }            
        return pm.mk_and(constraints);
    }

    proof_ref model_search::get_proof_trace(context const& ctx) {
        pred_transformer& pt = get_root().pt();
        ast_manager& m = pt.get_manager();
        datalog::context& dctx = ctx.get_context();
        datalog::rule_manager& rm = dctx.get_rule_manager();
        datalog::rule_unifier unifier(dctx);
        datalog::dl_decl_util util(m);
        datalog::rule_ref r0(rm), r1(rm);
        obj_map<expr, proof*> cache;
        obj_map<expr, datalog::rule*>  rules;
        ptr_vector<model_node> todo;
        proof_ref_vector trail(m);
        datalog::rule_ref_vector rules_trail(rm);
        proof* pr = 0;
        unifier.set_normalize(false);
        todo.push_back(m_root);
        update_models();
        while (!todo.empty()) {
            model_node* n = todo.back();
            TRACE("spacer", n->display(tout, 0););
            if (cache.find(n->state(), pr)) {
                todo.pop_back();
                continue;
            }
            ptr_vector<proof> pfs;
            ptr_vector<datalog::rule> rls;
            ptr_vector<model_node> const& chs = n->children();
            pfs.push_back(0);
            rls.push_back(0);
            for (unsigned i = 0; i < chs.size(); ++i) {
                if (cache.find(chs[i]->state(), pr)) {
                    pfs.push_back(pr);
                    rls.push_back(rules.find(chs[i]->state()));
                }
                else {
                    todo.push_back(chs[i]);
                }
            }            
            if (pfs.size() != 1 + chs.size()) {
                continue;
            }
            proof_ref rl(m);
            expr_ref_vector binding(m);
            n->mk_instantiate(r0, r1, binding);
            proof_ref p1(m), p2(m);
            p1 = r0->get_proof();
            if (!p1) {
                r0->display(dctx, std::cout);
            }
            SASSERT(p1);
            pfs[0] = p1;
            rls[0] = r1;
            TRACE("spacer",
                  tout << "root: " << mk_pp(p1.get(), m) << "\n";
                  for (unsigned i = 0; i < binding.size(); ++i) {
                      tout << mk_pp(binding[i].get(), m) << "\n";
                  }
                  for (unsigned i = 1; i < pfs.size(); ++i) {
                      tout << mk_pp(pfs[i], m) << "\n";
                  }
                  );
            datalog::rule_ref reduced_rule(rm), r3(rm);            
            reduced_rule = rls[0];
            // check if binding is identity.
            bool binding_is_id = true;
            for (unsigned i = 0; binding_is_id && i < binding.size(); ++i) {
                expr* v = binding[i].get();
                binding_is_id = is_var(v) && to_var(v)->get_idx() == i;
            }
            if (rls.size() > 1 || !binding_is_id) {
                expr_ref tmp(m);
                vector<expr_ref_vector> substs;
                svector<std::pair<unsigned,unsigned> > positions;
                substs.push_back(binding); // TODO base substitution.
                for (unsigned i = 1; i < rls.size(); ++i) {
                    datalog::rule& src = *rls[i];
                    bool unified = unifier.unify_rules(*reduced_rule, 0, src);
                    if (!unified) {
                        IF_VERBOSE(0,
                                   verbose_stream() << "Could not unify rules: ";
                                   reduced_rule->display(dctx, verbose_stream());
                                   src.display(dctx, verbose_stream()););
                    }
                    expr_ref_vector sub1 = unifier.get_rule_subst(*reduced_rule, true);
                    TRACE("spacer",
                          for (unsigned k = 0; k < sub1.size(); ++k) {
                              tout << mk_pp(sub1[k].get(), m) << " ";
                          }
                          tout << "\n";
                          );

                    for (unsigned j = 0; j < substs.size(); ++j) {
                        for (unsigned k = 0; k < substs[j].size(); ++k) {
                            var_subst(m, false)(substs[j][k].get(), sub1.size(), sub1.c_ptr(), tmp);
                            substs[j][k] = tmp;
                        }
                        while (substs[j].size() < sub1.size()) {
                            substs[j].push_back(sub1[substs[j].size()].get());
                        }
                    }

                    positions.push_back(std::make_pair(i,0));
                    substs.push_back(unifier.get_rule_subst(src, false));
                    VERIFY(unifier.apply(*reduced_rule.get(), 0, src, r3));
                    reduced_rule = r3;
                }

                expr_ref fml_concl(m);
                reduced_rule->to_formula(fml_concl);                    
                p1 = m.mk_hyper_resolve(pfs.size(), pfs.c_ptr(), fml_concl, positions, substs);

            }
            cache.insert(n->state(), p1);
            rules.insert(n->state(), reduced_rule);
            trail.push_back(p1);
            rules_trail.push_back(reduced_rule);
            todo.pop_back();
        }
        return proof_ref(cache.find(m_root->state()), m);
    }
*/

    model_search::~model_search() {
        TRACE("spacer", tout << "\n";);
        reset();
    }

    void model_search::reset() {
        if (m_root) {
            dealloc(m_root);
            m_root = 0;
        }
    }
/*
    void model_search::backtrack_level(bool uses_level, model_node& n) {
        SASSERT(m_root);
        if (uses_level && m_root->level() > n.level()) {
            IF_VERBOSE(2, verbose_stream() << "Increase level " << n.level() << "\n";);
            n.increase_level();
            enqueue_leaf(n);
        }
        else {
            model_node* p = n.parent();
            if (p) {
                set_leaf(*p);
            }               
        }     
    }
*/

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
          m_cancel(false),
          m_curr_model (0),
          m_mev (m)
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
            e = rels.insert_if_not_there2(pred, alloc(pred_transformer, *this, get_spacer_manager(), pred));            
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
                    pt = alloc(pred_transformer, *this, get_spacer_manager(), pred);
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
            pt = alloc(pred_transformer, *this, get_spacer_manager(), p);
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

    void context::validate() {
        if (!m_params.validate_result()) {
            return;
        }
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
                        throw default_exception(msg.str());
                    }
                }
            }
            TRACE ("spacer", tout << "Validation Succeeded\n";);
            break;
        }
        default:
            break;
        }
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

    lbool context::solve() {
        m_last_result = l_undef;
        try {
            solve_impl();
            UNREACHABLE();
        }
        catch (model_exception) {        
            //IF_VERBOSE(1, verbose_stream() << "\n"; m_search.display(verbose_stream()););  
            m_last_result = l_true;
            validate();

            if (m_params.print_statistics ()) {
                statistics st;
                collect_statistics (st);
                st.display_smt2 (verbose_stream ());
            }

            return l_true;
        }
        catch (inductive_exception) {
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
            decl2rel::iterator it = m_rels.begin (), end = m_rels.end ();
            for (; m_inductive_lvl > 0 && it != end; ++it) {
                if (it->m_value->head() != m_query_pred) {
                    it->m_value->propagate_to_infinity (m_inductive_lvl);	
                }
            }
            validate();

            if (m_params.print_statistics ()) {
                statistics st;
                collect_statistics (st);
                st.display_smt2 (verbose_stream ());
            }

            return l_false;
        }
        catch (unknown_exception) {
            return l_undef;
        }
        UNREACHABLE();
        return l_undef;
    }

    lbool context::solve_from_lvl (unsigned from_lvl) {
        m_last_result = l_undef;
        try {
            solve_impl_from_lvl (from_lvl);
            UNREACHABLE();
        }
        catch (model_exception) {        
            //IF_VERBOSE(1, verbose_stream() << "\n"; m_search.display(verbose_stream()););  
            m_last_result = l_true;
            validate();

            if (m_params.print_statistics ()) {
                statistics st;
                collect_statistics (st);
                st.display_smt2 (verbose_stream ());
            }

            return l_true;
        }
        catch (inductive_exception) {
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
            decl2rel::iterator it = m_rels.begin (), end = m_rels.end ();
            for (; m_inductive_lvl > 0 && it != end; ++it) {
                if (it->m_value->head() != m_query_pred) {
                    it->m_value->propagate_to_infinity (m_inductive_lvl);	
                }
            }
            validate();

            if (m_params.print_statistics ()) {
                statistics st;
                collect_statistics (st);
                st.display_smt2 (verbose_stream ());
            }

            return l_false;
        }
        catch (unknown_exception) {
            return l_undef;
        }
        UNREACHABLE();
        return l_undef;
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

/*
    model_ref context::get_model() {
        SASSERT(m_last_result == l_false);        
        expr_ref_vector refs(m);
        vector<relation_info> rs;
        model_ref md;
        get_level_property(m_inductive_lvl, refs, rs);            
        inductive_property ex(m, m_mc, rs);
        ex.to_model(md);
        return md;
    }

    proof_ref context::get_proof() const {
        datalog::scoped_proof _sc(m);
        proof_ref proof(m);
        SASSERT(m_last_result == l_true);
        proof = m_search.get_proof_trace(*this);
        TRACE("spacer", tout << "SPACER trace: " << mk_pp(proof, m) << "\n";);
        apply(m, m_pc.get(), proof);
        TRACE("spacer", tout << "SPACER trace: " << mk_pp(proof, m) << "\n";);
        // proof_utils::push_instantiations_up(proof);
        // TRACE("spacer", tout << "SPACER up: " << mk_pp(proof, m) << "\n";);
        return proof;
    }
*/


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
                child_pts.get (i)->get_spacer_manager ().formula_n2o (child_reach_facts->get (i), ofml, i);
                cex_ctx->assert_expr (ofml);
            }
            cex_ctx->assert_expr (pt->transition ());
            cex_ctx->assert_expr (pt->rule2tag (r));
            VERIFY (cex_ctx->check () == l_true);
            model_ref local_mdl;
            cex_ctx->get_model (local_mdl);
            cex_ctx->pop (1);

            for (unsigned i = 0; i < child_pts.size (); i++) {
                pred_transformer& ch_pt = *(child_pts.get (i));
                unsigned sig_size = ch_pt.sig_size ();
                expr_ref_vector ground_fact_conjs (m);
                expr_ref_vector ground_arg_vals (m);
                for (unsigned j = 0; j < sig_size; j++) {
                    expr_ref sig_arg (m), sig_val (m);
                    sig_arg = m.mk_const (ch_pt.get_spacer_manager ().o2o (ch_pt.sig (j), 0, i));
                    if (m_params.use_heavy_mev ()) {
                        m_mev.eval_heavy (local_mdl, sig_arg, sig_val);
                    }
                    else {
                        sig_val = m_mev.eval (local_mdl, sig_arg);
                    }
                    ground_fact_conjs.push_back (m.mk_eq (sig_arg, sig_val));
                    ground_arg_vals.push_back (sig_val);
                }
                if (ground_fact_conjs.size () > 0) {
                    expr_ref ground_fact (m);
                    ground_fact = m.mk_and (ground_fact_conjs.size (), ground_fact_conjs.c_ptr ());
                    ch_pt.get_spacer_manager ().formula_o2n (ground_fact, ground_fact, i);
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
    void context::solve_impl() 
    {
        //if there is no query predicate, abort
        if (!m_rels.find(m_query_pred, m_query)) {
            throw inductive_exception();            
        }

        //this is the outer loop of RECMC
        unsigned lvl = 0; //this is stack depth bound
        bool reachable = false;
        while (true) {
            checkpoint();
            m_expanded_lvl = lvl;
            m_stats.m_max_query_lvl = lvl;
            //model_node::reset_count (); // fresh counter for node ids

            reachable = check_reachability(lvl); //check bounded safety
            if (reachable) {
                throw model_exception();
            }

            //if bounded-safe, the check if summaries are
            //inductive. throws an exception if inductive
            if (lvl != 0) {
              propagate(m_expanded_lvl, lvl, UINT_MAX);
            }

            //this means summaries are not inductive. increase stack
            //depth bound and continue.
            lvl++;
            m_stats.m_max_depth = std::max(m_stats.m_max_depth, lvl);
            IF_VERBOSE(1,verbose_stream() << "Entering level "<<lvl << "\n";);
            IF_VERBOSE(1, 
                    if (m_params.print_statistics ()) {
                        statistics st;
                        collect_statistics (st);
                    };
                    );
        }
    }

    ///this is a variant of solve_impl that starts from stack depth
    ///from_lvl instead of zero
    void context::solve_impl_from_lvl (unsigned from_lvl) 
    {
        if (!m_rels.find(m_query_pred, m_query)) {
            throw inductive_exception();            
        }
        unsigned lvl = from_lvl;
        bool reachable;
        while (true) {
            checkpoint();
            m_expanded_lvl = lvl;
            m_stats.m_max_query_lvl = lvl;
            //model_node::reset_count (); // fresh counter for node ids
            reachable = check_reachability(lvl);
            if (reachable) {
                throw model_exception();
            }
            if (lvl != 0) {
              propagate(m_expanded_lvl, lvl, UINT_MAX);
            }
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
        model_node* root = alloc (model_node, 0, *m_query, level, 0, m_search);

        root->updt_post (post);
        m_search.set_root(root);            
        
        //keep picking the next goal and solving them. this is how the
        //selection of rules is determinized.
        while (model_node* node = m_search.next()) {
            IF_VERBOSE(2, verbose_stream() << "Expand node: " << node->level() << "\n";);
            checkpoint();
            expand_node(*node);   
        }
        return root->is_reachable ();
    }

/*  void context::close_node(model_node& n) {
        n.close();
        model_node* p = n.parent();
        while (p && p->is_1closed()) {
            p->close();
            p = p->parent();
        }
    }

    void context::check_pre_closed(model_node& n) {
        for (unsigned i = 0; i < n.children().size(); ++i) {
            if (!n.children()[i]->is_closed()) return;
        }
        n.set_pre_closed();
        model_node* p = n.parent();
        while (p && p->is_1closed()) {
            p->set_pre_closed();
            p = p->parent();
        }
    }
*/

    //this processes a goal and creates sub-goal
    void context::expand_node(model_node& n) 
    {
        SASSERT(n.is_open());
        
        if (n.level() < m_expanded_lvl) {
            m_expanded_lvl = n.level();
        }

        TRACE ("spacer", 
               tout << "expand-node: " << n.pt().head()->get_name() << " level: " << n.level() << "\n";
               tout << mk_pp(n.post(), m) << "\n";);

        //check if reachable by using existing UA.
        if (n.pt().is_reachable_known (n.post())) {
            TRACE("spacer", tout << "known to be reachable\n";);
            m_stats.m_num_reuse_reach++;
            n.close ();
            report_reach (n);
        }
        //otherwise check which of SUM/REACH/QUERY rule is applicable
        else {
            reset_curr_model ();
            // unreachable stuff
            unsigned uses_level = infty_level ();
            expr_ref_vector cube(m);
            // reachable stuff
            bool is_concrete;
            datalog::rule const* r = 0;
            vector<bool> reach_pred_used; // indicator vector denoting which predecessor's (along r) reach facts are used
            unsigned num_reuse_reach = 0;

            switch (expand_state(n, cube, uses_level, is_concrete, r, reach_pred_used, num_reuse_reach)) {
                //reachable but don't know if this is purely using UA
            case l_true: {
                // update stats
                m_stats.m_num_reuse_reach += num_reuse_reach;

                //if reachable using UA only
                if (is_concrete) {
                    // concretely reachable; infer new reach fact
                    TRACE ("spacer",
                            tout << "concretely reachable\n";
                          );
                    updt_as_reachable (n, *r);
                }
                //otherwise pick the first OA and create a sub-goal
                else {
                    TRACE ("spacer",
                            tout << "abstractly reachable\n";
                          );
                    create_children (n, *r, reach_pred_used);
                }
                break;
            }

                //query is not reachable, create new summary facts
            case l_false: {
                core_generalizer::cores cores;
                cores.push_back(std::make_pair(cube, uses_level));
                TRACE("spacer", tout << "cube:\n"; 
                      for (unsigned j = 0; j < cube.size(); ++j) tout << mk_pp(cube[j].get(), m) << "\n";);
                for (unsigned i = 0; !cores.empty() && i < m_core_generalizers.size(); ++i) {
                    core_generalizer::cores new_cores;                    
                    for (unsigned j = 0; j < cores.size(); ++j) {
                        (*m_core_generalizers[i])(n, cores[j].first, cores[j].second, new_cores);
                    }
                    cores.reset();
                    cores.append(new_cores);
                }
                for (unsigned i = 0; i < cores.size(); ++i) {
                    expr_ref_vector const& core = cores[i].first;
                    uses_level = cores[i].second;
                    expr_ref ncore(m_pm.mk_not_and(core), m);
                    TRACE("spacer", tout << "invariant state: " << (!is_infty_level(uses_level)?"":"(inductive) ") <<  mk_pp(ncore, m) << "\n";);
                    n.pt().add_property (ncore, uses_level);
                }
                CASSERT("spacer", n.level() == 0 || check_invariant(n.level()-1));
                n.close ();
                report_unreach (n);
                break;
            }
                //something went wrong
            case l_undef: {
                TRACE("spacer", tout << "unknown state: " << mk_pp(m_pm.mk_and(cube), m) << "\n";);
                throw unknown_exception();
            }
            }
        }
    }

    //
    // check if predicate transformer has a satisfiable predecessor state.
    // returns either a satisfiable predecessor state or 
    // return a property that blocks state and is implied by the 
    // predicate transformer (or some unfolding of it).
    // 
    lbool context::expand_state(model_node& n, expr_ref_vector& result, unsigned& uses_level, bool& is_concrete, datalog::rule const*& r, vector<bool>& reach_pred_used, unsigned& num_reuse_reach) {
        return n.pt().is_reachable(n, &result, uses_level, is_concrete, r, reach_pred_used, num_reuse_reach);
    }

  void context::propagate(unsigned min_prop_lvl, unsigned max_prop_lvl, unsigned full_prop_lvl) {    
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
              // XXX this can negatively affect convergence bound
              for (it = m_rels.begin (); it != end; ++it)
              {
                pred_transformer& r = *it->m_value;
                r.propagate_to_infinity (lvl);
              }
              if (lvl <= max_prop_lvl)
              {
                m_inductive_lvl = lvl;
                throw inductive_exception ();
              }
              break;
            }
        }
        if (m_params.simplify_formulas_post()) {            
            simplify_formulas();
        }
    }

    void context::mk_reach_fact (model_node& n, datalog::rule const& r, expr_ref& result, expr_ref_vector& child_reach_facts) {
        pred_transformer& pt = n.pt ();
        model_ref M (get_curr_model_ptr());

        ptr_vector<func_decl> preds;
        pt.find_predecessors (r, preds);

        expr_ref_vector path_cons (m);
        path_cons.push_back (pt.get_transition (r));
        app_ref_vector vars (m);

        for (unsigned i = 0; i < preds.size (); i++) {
            func_decl* pred = preds[i];
            pred_transformer& ch_pt = get_pred_transformer (pred);
            // get a reach fact of body preds used in the model
            expr_ref ch_reach (m), n_ch_reach (m);
            //ch_pt.get_all_used_o_reach_facts (M, i, ch_reach);
            ch_pt.get_used_o_reach_fact (M, i, ch_reach, n_ch_reach);
            TRACE ("spacer",
                    tout << mk_pp (ch_reach, m) << "\n";
                    expr_ref bval (m);
                    bval = m_mev.eval (M, ch_reach);
                    tout << "val in model: \n";
                    tout << mk_pp (bval, m) << "\n";
                  );
            DEBUG_CODE (
                expr_ref bval (m);
                if (m_params.use_heavy_mev ()) {
                    m_mev.eval_heavy (M, ch_reach, bval);
                }
                else {
                    bval = m_mev.eval (M, ch_reach);
                }
                SASSERT (m.is_true (bval));
            );
            path_cons.push_back (ch_reach);
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

        qe_project (m, vars, result, M);

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

       Introduce the shorthands:

       - T(x0,x1,x)   for transition
       - phi(x)       for n.post()
       - M(x0,x1,x)   for n.model()

       Assumptions:
         M => phi & T

       In other words, 
       1. phi & T is implied by M
       
       Goal is to find phi0(x0), phi1(x1) such that:

         phi(x) & phi0(x0) & phi1(x1) => T(x0, x1, x)       

       Strategy: 

       - Extract literals from T & phi using ternary simulation with M.
       - resulting formula is Phi.

       - perform cheap existential quantifier elimination on 
         Phi <- exists x . Phi(x0,x1,x)
         (e.g., destructive equality resolution) 
   
       - Sub-strategy 1: rename  remaining x to fresh variables.
       - Sub-strategy 2: replace remaining x to M(x).

       - For each literal L in result:

         - if L is x0 pure, add L to L0
         - if L is x1 pure, add L to L1
         - if L mixes x0, x1, add x1 = M(x1) to L1, add L(x1 |-> M(x1)) to L0
         
       - Create sub-goals for L0 and L1.

    */
    void context::create_children(model_node& n, datalog::rule const& r, vector<bool> const& reach_pred_used) {
        bool use_model_generalizer = m_params.use_model_generalizer();
 
        pred_transformer& pt = n.pt();
        model_ref M = get_curr_model_ptr();
        expr* T   = pt.get_transition(r);
        expr* phi = n.post();

        TRACE("spacer", 
              tout << "Model:\n";
              model_smt2_pp(tout, m, *M, 0);
              tout << "\n";
              tout << "Transition:\n" << mk_pp(T, m) << "\n";
              tout << "Phi:\n" << mk_pp(phi, m) << "\n";);

        SASSERT (r.get_uninterpreted_tail_size () > 0);
        /**
         * if (r.get_uninterpreted_tail_size () == 0) {
         *     updt_as_reachable (n, r);
         *     return;
         * }
         */

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

        qe::flatten_and(forms);        
        ptr_vector<expr> forms1(forms.size(), forms.c_ptr());
        model_evaluator mev(m);
        if (use_model_generalizer) {
            Phi.append(mev.minimize_model(forms1, M));
        }
        else {
            mev.minimize_literals(forms1, M, Phi);
        }
        //pt.remove_predecessors (Phi);

        app_ref_vector vars(m);
        unsigned sig_size = pt.head()->get_arity();
        for (unsigned i = 0; i < sig_size; ++i) {
            vars.push_back(m.mk_const(m_pm.o2n(pt.sig(i), 0)));
        }
        ptr_vector<app>& aux_vars = pt.get_aux_vars(r);
        vars.append(aux_vars.size(), aux_vars.c_ptr());

        expr_ref phi1 = m_pm.mk_and (Phi);
        qe_project (m, vars, phi1, M, true);
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
        
        // create a new derivation for the model
        // order the pts -- for now, right to left
        bool r_to_l = (m_params.order_children() == 0);
        vector<unsigned> o_idx;
        vector<bool> reach_pred_used1;
        pred_pts.reset ();
        ptr_vector<func_decl>::iterator it;
        for (ptr_vector<func_decl>::iterator fwd_it = preds.begin ();
                fwd_it != preds.end (); fwd_it++) {

            if (r_to_l) { it = fwd_it; }
            else { it = preds.begin () + (preds.end () - fwd_it - 1); }

            pred_pts.push_back (&get_pred_transformer (*it));
            o_idx.push_back (it-preds.begin ());
            reach_pred_used1.push_back (reach_pred_used.get (it-preds.begin ()));
        }
        derivation* deriv = alloc (derivation, &n, pred_pts, reach_pred_used1, o_idx, r, m_search, *this);
        n.add_deriv (deriv);
        deriv->setup (phi1, M);
        SASSERT (deriv->has_next ());

        // create post for the first child and add to queue
        model_node* ch = deriv->mk_next ();
        m_search.add_leaf (*ch);
        m_stats.m_num_queries++;
    }

    void context::report_reach (model_node& ch) {
        TRACE ("spacer",
                tout << ch.pt ().head ()->get_name () << " : "
                     << "post : " << mk_pp (ch.post (), m)
                     << " is reachable\n";
              );

        ch.set_reachable ();
        SASSERT (ch.is_closed ());

        model_node* par = ch.parent ();
        derivation* deriv = ch.my_deriv ();

        // ch == root
        if (!deriv) {
            ch.del_derivs ();
            return;
        }
        SASSERT (par);

        if (deriv->has_next ()) deriv->updt_setup ();

        model_node* sib;

        // create post for the next child, if any
        sib = deriv->mk_next ();

        if (!sib) { // nothing left to derive
            // get a model
            pred_transformer& par_pt = par->pt ();
            datalog::rule const& r = deriv->get_rule ();
            VERIFY (par_pt.is_reachable_with_reach_facts (*par, r));
            // get reach fact using model
            updt_as_reachable (*par, r);
        }
        else {
            SASSERT (sib);
            m_search.add_leaf (*sib);
            m_stats.m_num_queries++;
        }
    }

    void context::updt_as_reachable (model_node& n, datalog::rule const& r) {
        expr_ref reach_fact (m);
        expr_ref_vector child_reach_facts (m);
        mk_reach_fact (n, r, reach_fact, child_reach_facts);
        n.pt ().add_reach_fact (reach_fact, r, child_reach_facts);
        if (n.is_inq ()) m_search.erase_leaf (n);
        n.close ();
        report_reach (n);
    }

    void context::report_unreach (model_node& ch) {
        TRACE ("spacer",
                tout << ch.pt ().head ()->get_name () << " : "
                     << "post : " << mk_pp (ch.post (), m)
                     << " is unreachable\n";
              );

        // TODO: how does this new knowledge that ch has a proof
        // affect any existing derivations?

        ch.set_unreachable ();

        model_node* par = ch.parent ();
        derivation* deriv = ch.my_deriv ();

        SASSERT (ch.is_closed ());

        // ch == root
        if (!deriv) {
            ch.del_derivs ();
            return;
        }

        SASSERT (par);

        par->del_derivs (deriv);

        // an aggressive step
        // ch_pt has new lemmas at ch_level; delete all affected derivations
        // TODO: ch_pt could have learnt lemmas at a level higher than ch_level
        // -- check for that??
        //pred_transformer const& ch_pt = ch.pt ();
        //unsigned ch_level = ch.level ();
        //par->del_derivs (ch_pt, ch_level);

        if (!par->has_derivs (par->level ()-1)) {
            TRACE ("spacer", tout << "No more normal derivations\n";);
            if (!par->is_inq ()) m_search.add_leaf (*par);
        }
        // o.w. there are other running derivations...
    }

    // TODO: better check?
    bool context::redo_at_higher_level (model_node const& ch, derivation const* d, model_node const& par) const {
        return false;
        unsigned ch_level = ch.level ();
        unsigned root_level = m_search.get_root ().level ();
        return (ch_level < root_level && // level can be increased
                d->is_closed ());        // all premises up to (and incl.) ch are closed
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
