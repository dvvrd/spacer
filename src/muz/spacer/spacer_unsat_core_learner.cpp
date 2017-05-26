
#include "spacer_unsat_core_learner.h"

#include "spacer_unsat_core_plugin.h"

#include "proof_utils.h"
#include "for_each_expr.h"

namespace spacer
{

#pragma mark - proof iterators
    
    ProofIteratorPostOrder::ProofIteratorPostOrder(proof* root, ast_manager& manager) : m(manager)
    {
        todo.push_back(root);
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
            proof* currentNode = todo.back();
            
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
                        todo.push_back(premise);
                        existsUnvisitedParent = true;
                    }
                }
                
                // if we already visited all parent-inferences, we can visit the inference too
                if (!existsUnvisitedParent)
                {
                    visited.mark(currentNode, true);
                    todo.pop_back();
                    return currentNode;
                }
            }
            else
            {
                todo.pop_back();
            }
        }
        
        // we have already iterated through all inferences
        return nullptr;
    }
    
    
# pragma mark - main methods
unsat_core_learner::~unsat_core_learner()
{
    for (int i=0; i < m_plugins.size(); ++i)
    {
        m_plugins[i]->~unsat_core_plugin();
    }
}

void unsat_core_learner::register_plugin(unsat_core_plugin* plugin)
{
    m_plugins.push_back(plugin);
}

void unsat_core_learner::compute_unsat_core(proof *root, expr_set& asserted_b, expr_ref_vector& unsat_core)
{
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
                    if (!only_contains_symbols_b(m.get_fact(currentNode)))
                    {
                        m_a_mark.mark(currentNode, true);
                    }
                    else
                    {
                        SASSERT(false);
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
    
    // TODO: remove duplicates from unsat core?
    
    // move all lemmas into vector
    for (auto it = m_unsat_core.begin(); it != m_unsat_core.end(); ++it)
    {
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

#pragma mark - API

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
    
    void unsat_core_learner::add_lemma_to_core(expr_ref lemma)
    {
        IF_VERBOSE(2, verbose_stream() << "Add lemma to unsat core:" << mk_pp(lemma, m) << " " << lemma->get_id() << "\n";);
        m_unsat_core.push_back(lemma);
    }

# pragma mark - checking for b_symbols
    
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

void unsat_core_learner::collect_symbols_b(expr_set axioms_b)
{
    expr_mark visited;
    collect_pure_proc proc(m_symbols_b);
    for (auto it = axioms_b.begin(); it != axioms_b.end(); ++it)
    {
        for_each_expr(proc, visited, *it);
    }
}

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

bool unsat_core_learner::only_contains_symbols_b(expr* expr) const
{
    is_pure_expr_proc proc(m_symbols_b, m);
    try {
        for_each_expr(proc, expr);
    }
    catch (is_pure_expr_proc::non_pure)
    {
        return false;
    }
    return true;
}



}
