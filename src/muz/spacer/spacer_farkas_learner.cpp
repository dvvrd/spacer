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
// TODO: what to write here
--*/

//TODO: reorder, delete unnecessary includes
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
#include "proof_utils.h"
#include "reg_decl_plugins.h"
#include "smt_farkas_util.h"

namespace spacer {

    //TODO: constness
#pragma mark - proof iterators
    
    ProofIteratorPostOrder::ProofIteratorPostOrder(proof* root, ast_manager& manager) : m(manager)
    {
        todo.push(root);
    }
    
    bool ProofIteratorPostOrder::hasNext()
    {
        return !todo.empty();
    }
    
    /*
     * iterative post-order depth-first search (DFS) through the proof DAG
     */
    proof* ProofIteratorPostOrder::next()
    {
        while (!todo.empty())
        {
            proof* currentNode = todo.top();
            
            // if we haven't already visited the current unit
            if (!visited.is_marked(currentNode))
            {
                bool existsUnvisitedParent = false;
                
                // add unprocessed premises to stack for DFS. If there is at least one unprocessed premise, don't compute the result
                // for currentProof now, but wait until those unprocessed premises are processed.
                for (unsigned i = 0; i < m.get_num_parents(currentNode); ++i)
                {
                    SASSERT(m.is_proof(currentNode->get_arg(i)));
                    proof* premise = to_app(currentNode->get_arg(i));
                
                    // if we haven't visited the current premise yet
                    if(!visited.is_marked(premise))
                    {
                        // add it to the stack
                        todo.push(premise);
                        existsUnvisitedParent = true;
                    }
                }
                
                // if we already visited all parent-inferences, we can visit the inference too
                if (!existsUnvisitedParent)
                {
                    visited.mark(currentNode, true);
                    todo.pop();
                    return currentNode;
                }
            }
            else
            {
                todo.pop();
            }
        }
        
        // we have already iterated through all inferences
        return nullptr;
    }
    
    
# pragma mark - main methods
    
    void unsat_core_learner::register_plugin(std::shared_ptr<unsat_core_plugin> plugin)
    {
        m_plugins.push_back(plugin);
    }
    
    void unsat_core_learner::compute_unsat_core(proof *root, expr_set& asserted_b, expr_ref_vector& unsat_core)
    {
        // TODO: check that everything is reset?
        
        // transform proof in order to get a proof which is better suited for unsat-core-extraction
        proof_ref pr(root, m);
        proof_utils::reduce_hypotheses(pr);
        proof_utils::permute_unit_resolution(pr);
        IF_VERBOSE(3, verbose_stream() << "Reduced proof:\n" << mk_ismt2_pp(pr, m) << "\n";);
        
        // compute symbols occuring in B
        collect_symbols_b(asserted_b);
        
        // traverse proof
        ProofIteratorPostOrder it(root, m);
        while (it.hasNext())
        {
            proof* currentNode = it.next();
//            verbose_stream() << mk_pp(m.get_fact(currentNode), m) << std::endl;
            
            if (m.get_num_parents(currentNode) == 0)
            {
                switch(currentNode->get_decl_kind())
                {
                    
                    case PR_ASSERTED: // currentNode is an axiom
                    {
                        if (asserted_b.contains(m.get_fact(currentNode)))
                        {
                            m_b_mark.mark(currentNode, true);
                        }
                        else
                        {
                            m_a_mark.mark(currentNode, true);
                        }
                        break;
                    }
                    // currentNode is a hypothesis:
                    case PR_HYPOTHESIS:
                    {
                        m_h_mark.mark(currentNode, true);
                        break;
                    }
                    /*
                     * currentNode is result of skolemization
                     */
                    case PR_DEF_AXIOM:
                    {
                        // TODO: what to do here? check proofChecker!
                        // BUG: is this correct?
                        if (only_contains_symbols_b(m.get_fact(currentNode)))
                        {
                            m_b_mark.mark(currentNode, true);
                        }
                        else
                        {
                            m_a_mark.mark(currentNode, true);
                        }
                        break;
                    }
                    default:
                    {
                        break;
                    }
                }
            }
            else
            {
                // collect from parents whether derivation of current node contains A-axioms, B-axioms and hypothesis
                bool need_to_mark_a = false;
                bool need_to_mark_b = false;
                bool need_to_mark_h = false;
                bool need_to_mark_closed = true;
                
                for (unsigned i = 0; i < m.get_num_parents(currentNode); ++i)
                {
                    SASSERT(m.is_proof(currentNode->get_arg(i)));
                    proof* premise = to_app(currentNode->get_arg(i));
                    
                    need_to_mark_a = need_to_mark_a || m_a_mark.is_marked(premise);
                    need_to_mark_b = need_to_mark_b || m_b_mark.is_marked(premise);
                    need_to_mark_h = need_to_mark_h || m_h_mark.is_marked(premise);
                    need_to_mark_closed = need_to_mark_closed && m_closed.is_marked(premise);
                }
                
                // if current node is application of lemma, we know that all hypothesis are removed
                if(currentNode->get_decl_kind() == PR_LEMMA)
                {
                    need_to_mark_h = false;
                }
                
                // save results
                m_a_mark.mark(currentNode, need_to_mark_a);
                m_b_mark.mark(currentNode, need_to_mark_b);
                m_h_mark.mark(currentNode, need_to_mark_h);
            }
            
            // we have now collected all necessary information, so we can visit the node
            // if the node mixes A-reasoning and B-reasoning and contains non-closed premises
            if (m_a_mark.is_marked(currentNode) && m_b_mark.is_marked(currentNode) && !m_closed.is_marked(currentNode))
            {
                compute_partial_core(currentNode); // then we need to compute a partial core
                SASSERT(!(m_a_mark.is_marked(currentNode) && m_b_mark.is_marked(currentNode)) ||
                        m_closed.is_marked(currentNode));
            }
        }
        
        // give plugins chance to finalize their unsat-core-computation
        finalize();
        
        // move all lemmas from set into vector
        for (auto it = m_unsat_core_set.begin(); it != m_unsat_core_set.end(); ++it)
        {
            IF_VERBOSE(2, verbose_stream() << "Move lemma to unsat core vector:" << mk_pp(*it, m) << " " << (*it)->get_id() << "\n";);
            unsat_core.push_back(*it);
        }
    }
    
    void unsat_core_learner::compute_partial_core(proof* step)
    {
        for (auto it=m_plugins.begin(); it != m_plugins.end(); ++it)
        {
            auto plugin = *it;
            plugin->compute_partial_core(step);
        }
    }
    
    void unsat_core_learner::finalize()
    {
        for (auto it=m_plugins.begin(); it != m_plugins.end(); ++it)
        {
            auto plugin = *it;
            plugin->finalize();
        }
    }
    
#pragma mark - getter / setter
    
    bool unsat_core_learner::is_a_marked(proof* p)
    {
        return m_a_mark.is_marked(p);
    }
    bool unsat_core_learner::is_b_marked(proof* p)
    {
        return m_b_mark.is_marked(p);
    }
    bool unsat_core_learner::is_h_marked(proof* p)
    {
        return m_h_mark.is_marked(p);
    }
    bool unsat_core_learner::is_closed(proof*p)
    {
        return m_closed.is_marked(p);
    }
    void unsat_core_learner::set_closed(proof* p, bool value)
    {
        m_closed.mark(p, value);
    }
    
    
    void unsat_core_learner::collect_symbols_b(expr_set axioms_b)
    {
        for (auto it = axioms_b.begin(); it != axioms_b.end(); ++it)
        {
            expr* possibly_app = *it;
            if (is_app(possibly_app))
            {
                app* app = to_app(possibly_app);
                if (app->get_family_id() == null_family_id)
                {
                    m_symbols_b.insert(app->get_decl());
                }
            }
        }
    }
    
    bool unsat_core_learner::only_contains_symbols_b(expr* expr) const
    {
        if (is_app(expr))
        {
            app* app = to_app(expr);
            if (app->get_family_id() == null_family_id)
            {
                array_util util(m);
                if (m_symbols_b.find(app->get_decl()) == m_symbols_b.end())
                {
                    return false;
                }
                if (app->get_family_id () == util.get_family_id () &&
                    app->is_app_of(app->get_family_id (), OP_ARRAY_EXT))
                {
                    return false;
                }
            }
        }
        return true;
    }
    
    void unsat_core_learner::add_lemma_to_core(expr_ref lemma)
    {
        IF_VERBOSE(2, verbose_stream() << "Add lemma to unsat core:" << mk_pp(lemma, m) << " " << lemma->get_id() << "\n";);
        m_unsat_core_set.insert_if_not_there(lemma);
    }
    
#pragma mark - unsat_core_plugin_lemma

    void unsat_core_plugin_lemma::compute_partial_core(proof* step)
    {
        SASSERT(m_learner.is_a_marked(step));
        SASSERT(m_learner.is_b_marked(step));
        
        for (unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
        {
            SASSERT(m_learner.m.is_proof(step->get_arg(i)));
            proof* premise = to_app(step->get_arg(i));

            if (m_learner.is_b_marked(premise) && !m_learner.is_closed(premise))
            {
                SASSERT(!m_learner.is_a_marked(premise));
                add_lowest_split_to_core(premise);
            }
        }
        m_learner.set_closed(step, true);
    }
    
    void unsat_core_plugin_lemma::add_lowest_split_to_core(proof* step) const
    {
        std::stack<proof*> todo;
        todo.push(step);
        
        while (!todo.empty())
        {
            proof* current = todo.top();
            todo.pop();
            
            // if current step hasn't been processed,
            if (!m_learner.is_closed(current))
            {
                m_learner.set_closed(current, true);
                SASSERT(!m_learner.is_a_marked(current)); // by I.H. the step must be already visited
                
                // and the current step needs to be interpolated:
                if (m_learner.is_b_marked(current))
                {
                    expr* fact = m_learner.m.get_fact(current);
                    // if we trust the current step and we are able to use it
                    if (m_learner.only_contains_symbols_b(fact) && !m_learner.is_h_marked(current))
                    {
                        // just add it to the core
                        m_learner.add_lemma_to_core(expr_ref(fact, m_learner.m));
                    }
                    // otherwise recurse on premises
                    else
                    {
                    
                        for (unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
                        {
                            SASSERT(m_learner.m.is_proof(step->get_arg(i)));
                            proof* premise = to_app(step->get_arg(i));
                            todo.push(premise);
                        }
                    }
                }
            }
        }
    }

    
#pragma mark - unsat_core_plugin_farkas_lemma
    void unsat_core_plugin_farkas_lemma::compute_partial_core(proof* step)
    {
        SASSERT(m_learner.is_a_marked(step));
        SASSERT(m_learner.is_b_marked(step));
        
        func_decl* d = step->get_decl();
        symbol sym;
        if(!m_learner.is_closed(step) && // if step is not already interpolated
           step->get_decl_kind() == PR_TH_LEMMA && // and step is a Farkas lemma
           d->get_num_parameters() >= 2 && // the Farkas coefficients are saved in the parameters of step
           d->get_parameter(0).is_symbol(sym) && sym == "arith" && // the first two parameters are "arith", "farkas",
           d->get_parameter(1).is_symbol(sym) && sym == "farkas" &&
           d->get_num_parameters() >= m_learner.m.get_num_parents(step) + 2) // the following parameters are the Farkas coefficients
        {
            SASSERT(m_learner.m.has_fact(step));
            
            bool needsToBeClosed = true;
            
            std::vector<app*> literals;
            std::vector<rational> coefficients;
            
            /* We need two workarounds:
             * 1) Although we know from theory, that the Farkas coefficients are always nonnegative,
             * the Farkas coefficients provided by arith_core are sometimes negative (must be a bug)
             * as workaround we take the absolute value of the provided coefficients.
             * 2) The theory lemmas should actually be seen as an axiom (i.e. a rule without premise).
             * Since the conclusion of such a theory lemma is a disjunction, one can also add several
             * or all of those disjuncts as negated premise instead of putting them as disjunct into the conclusion.
             * The lemma provided by arith_core does both, so as a workaround we need to deal with all those
             * situations.
             */
            parameter const* params = d->get_parameters() + 2; // point to the first Farkas coefficient
            
            for(unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
            {
                SASSERT(m_learner.m.is_proof(step->get_arg(i)));
                proof * premise = to_app(step->get_arg(i));
                
                if (m_learner.is_b_marked(premise) && !m_learner.is_closed(premise))
                {
                    SASSERT(!m_learner.is_a_marked(premise));
                    
                    if (m_learner.only_contains_symbols_b(m_learner.m.get_fact(step)) && !m_learner.is_h_marked(step))
                    {
                        m_learner.set_closed(premise, true);
                        
                        rational coefficient;
                        VERIFY(params[i].is_rational(coefficient));
                        literals.push_back(to_app(m_learner.m.get_fact(premise)));
                        coefficients.push_back(abs(coefficient));
                    }
                    else // otherwise we don't deal with the premise, so we don't need to close the current step at the end
                    {
                        needsToBeClosed = false;
                    }
                }
            }
            params += m_learner.m.get_num_parents(step); // point to the first Farkas coefficient, which corresponds to a formula in the conclusion
            
            // TODO: possible BUG: why do we always trust the conclusion, in contrast to the premises? i.e. why don't we need to check for
            // learner.only_contains_symbols_b(learner.m.get_fact(step)) && !learner.is_h_marked(step)?
            // if there are still parameters left, we know that the conclusion is not the empty clause, but contains negated premises (valid, since A land B land C => bot is the same as A => neg B lor neg C)
            // the conclusion can either be a single formula or a disjunction of several formulas, we have to deal with both situations
            if (m_learner.m.get_num_parents(step) + 2 < d->get_num_parameters())
            {
                unsigned num_args = 1;
                expr* conclusion = m_learner.m.get_fact(step);
                expr* const* args = &conclusion;
                if (m_learner.m.is_or(conclusion))
                {
                    app* _or = to_app(conclusion);
                    num_args = _or->get_num_args();
                    args = _or->get_args();
                }
                SASSERT(m_learner.m.get_num_parents(step) + 2 + num_args == d->get_num_parameters());
                
                bool_rewriter rewriter(m_learner.m);
                for (unsigned i = 0; i < num_args; ++i)
                {
                    expr* premise = args[i];
                    
                    expr_ref negatedPremise(m_learner.m);
                    rewriter.mk_not(premise, negatedPremise);
                    SASSERT(is_app(negatedPremise));
                    literals.push_back(to_app(negatedPremise));
                    
                    rational coefficient;
                    VERIFY(params[i].is_rational(coefficient));
                    coefficients.push_back(abs(coefficient));
                }
            }
            
            // now all B-pure literals and their coefficients are collected, so compute the linear combination
            expr_ref res(m_learner.m);
            compute_linear_combination(coefficients, literals, res);

            m_learner.add_lemma_to_core(res);
            
            if (needsToBeClosed)
            {
                m_learner.set_closed(step, true);
            }
        }
    }

    
    void unsat_core_plugin_farkas_lemma::compute_linear_combination(const std::vector<rational>& coefficients, const std::vector<app*>& literals, expr_ref& res)
    {
        SASSERT(literals.size() == coefficients.size());
        
        ast_manager& m = res.get_manager();
        smt::farkas_util util(m);
        // TODO: util.set_split_literals (m_split_literals); // small optimization: if flag m_split_literals is set, then preserve diff constraints
        for(unsigned i = 0; i < literals.size(); ++i)
        {
            util.add(coefficients[i], literals[i]);
        }
        res = util.get();
    }



    
#pragma mark - old code, to be deleted
    
    
    
    

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
                            TRACE("farkas_learner2",
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

                TRACE("farkas_learner2",
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
                    TRACE("farkas_learner2", tout << "Add: " << mk_pp(res, m) << "\n";);
                    INSERT(res);
                    b_closed.mark(p, true);
                }
            }
            default:
                break;
            }
        }

        std::for_each(hyprefs.begin(), hyprefs.end(), delete_proc<expr_set>());
        simplify_bounds(lemmas);
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
                TRACE("farkas_learner2", 
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
    }
}

