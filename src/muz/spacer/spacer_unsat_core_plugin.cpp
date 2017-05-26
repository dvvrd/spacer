#include "spacer_unsat_core_plugin.h"

#include "spacer_unsat_core_learner.h"

#include "smt_farkas_util.h"
#include "bool_rewriter.h"

namespace spacer
{
    
#pragma mark - unsat_core_plugin
unsat_core_plugin::~unsat_core_plugin(){}

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
    ptr_vector<proof> todo;
    todo.push_back(step);
    
    while (!todo.empty())
    {
        proof* current = todo.back();
        todo.pop_back();
        
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
                        todo.push_back(premise);
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
        
        
        ptr_vector<app> literals;
        vector<rational> coefficients;
        
        /* The farkas lemma represents a subproof starting from premise(-set)s A, BNP and BP(ure) and
         * ending in a disjunction D. We need to compute the contribution of BP, i.e. a formula, which
         * is entailed by BP and together with A and BNP entails D.
         *
         * Let Fark(F) be the farkas coefficient for F. We can use the fact that
         * (A*Fark(A) + BNP*Fark(BNP) + BP*Fark(BP) + (neg D)*Fark(D)) => false. (E1)
         * We further have that A+B => C implies (A \land B) => C. (E2)
         *
         * Alternative 1:
         * From (E1) immediately get that BP*Fark(BP) is a solution.
         *
         * Alternative 2:
         * We can rewrite (E2) to rewrite (E1) to
         * (BP*Fark(BP)) => (neg(A*Fark(A) + BNP*Fark(BNP) + (neg D)*Fark(D))) (E3)
         * and since we can derive (A*Fark(A) + BNP*Fark(BNP) + (neg D)*Fark(D)) from
         * A, BNP and D, we also know that it is inconsisent. Therefore
         * neg(A*Fark(A) + BNP*Fark(BNP) + (neg D)*Fark(D)) is a solution.
         *
         * Finally we also need the following workaround:
         * 1) Although we know from theory, that the Farkas coefficients are always nonnegative,
         * the Farkas coefficients provided by arith_core are sometimes negative (must be a bug)
         * as workaround we take the absolute value of the provided coefficients.
         */
        parameter const* params = d->get_parameters() + 2; // point to the first Farkas coefficient
        
        IF_VERBOSE(3, verbose_stream() << "Farkas input: "<< "\n";);
        for (unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
        {
            SASSERT(m_learner.m.is_proof(step->get_arg(i)));
            proof *prem = to_app(step->get_arg(i));
            
            rational coef;
            VERIFY(params[i].is_rational(coef));
            bool b_pure = m_learner.only_contains_symbols_b(m_learner.m.get_fact(prem)) && !m_learner.is_h_marked(prem);
            IF_VERBOSE(3, verbose_stream() << (b_pure?"B":"A") << " " << coef << " " << mk_pp(m_learner.m.get_fact(prem), m_learner.m) << "\n";);
        }
        
        
        bool needsToBeClosed = true;
        
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
                    
                    if (!m_use_constant_from_a)
                    {
                        rational coefficient;
                        VERIFY(params[i].is_rational(coefficient));
                        literals.push_back(to_app(m_learner.m.get_fact(premise)));
                        coefficients.push_back(abs(coefficient));
                    }
                }
                else
                {
                    needsToBeClosed = false;
                    
                    if (m_use_constant_from_a)
                    {
                        rational coefficient;
                        VERIFY(params[i].is_rational(coefficient));
                        literals.push_back(to_app(m_learner.m.get_fact(premise)));
                        coefficients.push_back(abs(coefficient));
                    }
                }
            }
            else
            {
                if (m_use_constant_from_a)
                {
                    rational coefficient;
                    VERIFY(params[i].is_rational(coefficient));
                    literals.push_back(to_app(m_learner.m.get_fact(premise)));
                    coefficients.push_back(abs(coefficient));
                }
            }
        }
        
        if (m_use_constant_from_a)
        {
            params += m_learner.m.get_num_parents(step); // point to the first Farkas coefficient, which corresponds to a formula in the conclusion
            
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
        }
        
        // only close step if there are no non-pure steps
        if (needsToBeClosed)
        {
            m_learner.set_closed(step, true);
        }
        
        // now all B-pure literals and their coefficients are collected, so compute the linear combination
        expr_ref res(m_learner.m);
        compute_linear_combination(coefficients, literals, res);
        
        m_learner.add_lemma_to_core(res);
    }
}

void unsat_core_plugin_farkas_lemma::compute_linear_combination(const vector<rational>& coefficients, const ptr_vector<app>& literals, expr_ref& res)
{
    SASSERT(literals.size() == coefficients.size());
    
    ast_manager& m = res.get_manager();
    smt::farkas_util util(m);
    util.set_split_literals (m_split_literals); // small optimization: if flag m_split_literals is set, then preserve diff constraints
    for(unsigned i = 0; i < literals.size(); ++i)
    {
        util.add(coefficients[i], literals[i]);
    }
    res = util.get();
}

}
