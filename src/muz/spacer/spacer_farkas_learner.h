/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_farkas_learner.h

Abstract:

    SMT2 interface for the datalog SPACER

Author:

    Krystof Hoder (t-khoder) 2011-11-1.

Revision History:

--*/

#ifndef _SPACER_FARKAS_LEARNER_H_
#define _SPACER_FARKAS_LEARNER_H_

#include "ast.h"
#include <vector>
#include <stack>
#include <unordered_set>
#include <unordered_map>

namespace spacer {


    
    /*
     * iterator, which traverses the proof in depth-first post-order.
     */
    class ProofIteratorPostOrder
    {
    public:
        ProofIteratorPostOrder(proof* refutation, ast_manager& manager);
        bool hasNext();
        proof* next();
        
    private:
        ptr_vector<proof> todo;
        ast_mark visited; // the proof nodes we have already visited
        
        ast_manager& m;
    };
    
    class unsat_core_plugin; // forward declaration for unsat_core_learner
    class unsat_core_learner {
        typedef obj_hashtable<expr> expr_set;

    public:
        unsat_core_learner(ast_manager& m) : m(m), m_unsat_core(m) {};
        ast_manager& m;

        /*
         * register a plugin for computation of partial unsat cores
         * currently plugins are called in the order they have been registered
         */
        void register_plugin(std::shared_ptr<unsat_core_plugin> plugin);

        /*
         * compute unsat core using the registered unsat-core-plugins
         */
        void compute_unsat_core(proof* root, expr_set& asserted_b, expr_ref_vector& unsat_core);
        
        /*
         * getter/setter methods for data structures exposed to plugins
         * the following invariants can be assumed and need to be maintained by the plugins:
         *  - a node is a-marked iff it is derived using at least one asserted proof step from A.
         *  - a node is b-marked iff its derivation contains no asserted proof steps from A and
         *    no hypothesis (with the additional complication that lemmas conceptually remove hypothesis)
         *  - a node is h-marked, iff it is derived using at least one hypothesis
         *  - a node is closed, iff it has already been interpolated, i.e. its contribution is
         *    already covered by the unsat-core.
         */
        bool is_a_marked(proof* p);
        bool is_b_marked(proof* p);
        bool is_h_marked(proof* p);
        bool is_closed(proof* p);
        void set_closed(proof* p, bool value);
        
        /*
         * helper method, which can be used by plugins
         * returns true iff all symbols of expr occur in some b-asserted formula.
         * must only be called after a call to collect_symbols_b.
         */
        bool only_contains_symbols_b(expr* expr) const;

        /*
         * adds a lemma to the unsat core
         */
        void add_lemma_to_core(expr_ref lemma);
        
    private:
        std::vector<std::shared_ptr<unsat_core_plugin> > m_plugins; // the registered plugins
        std::unordered_set<func_decl*> m_symbols_b; // symbols, which occur in any b-asserted formula
        void collect_symbols_b(expr_set axioms_b);
        
        ast_mark m_a_mark;
        ast_mark m_b_mark;
        ast_mark m_h_mark;
        ast_mark m_closed;

        expr_ref_vector m_unsat_core; // collects the lemmas of the unsat-core, will at the end be inserted into unsat_core.

        /*
         * computes partial core for step by delegating computation to plugins
         */
        void compute_partial_core(proof* step);
        
        /*
         * finalize computation of unsat-core
         */
        void finalize();
    };
    
    
    class unsat_core_plugin {
        
    public:
        unsat_core_plugin(unsat_core_learner& learner) : m_learner(learner){};
        virtual void compute_partial_core(proof* step) = 0;
        virtual void finalize(){};
    
        unsat_core_learner& m_learner;
    };
    
    
    class unsat_core_plugin_lemma : public unsat_core_plugin {
        
    public:
        unsat_core_plugin_lemma(unsat_core_learner& learner) : unsat_core_plugin(learner){};
        virtual void compute_partial_core(proof* step) override;
        
    private:
        void add_lowest_split_to_core(proof* step) const;
    };
    
    
    class unsat_core_plugin_farkas_lemma : public unsat_core_plugin {
        
    public:
        unsat_core_plugin_farkas_lemma(unsat_core_learner& learner) : unsat_core_plugin(learner){};
        virtual void compute_partial_core(proof* step) override;
        
    private:
        /*
         * compute linear combination of literals 'literals' having coefficients 'coefficients' and save result in res
         */
        void compute_linear_combination(const std::vector<rational>& coefficients, const std::vector<app*>& literals, expr_ref& res);
    };
    
    
    
    
class farkas_learner {
    typedef obj_hashtable<expr> expr_set;

    bool m_split_literals;
    
    void combine_constraints(unsigned cnt, app * const * constrs, rational const * coeffs, expr_ref& res);

    bool is_farkas_lemma(ast_manager& m, expr* e);
   
    void get_asserted(proof* p, expr_set const& bs, ast_mark& b_closed, obj_hashtable<expr>& lemma_set, expr_ref_vector& lemmas);

    bool is_pure_expr(func_decl_set const& symbs, expr* e, ast_manager& m) const;

public:
    farkas_learner(): m_split_literals (false) {}

    /**
        Traverse a proof and retrieve lemmas using the vocabulary from bs.
    */
    void get_lemmas(proof* root, expr_set const& bs, expr_ref_vector& lemmas);

    void collect_statistics(statistics& st) const {} 
    void reset_statistics () {}
  

    /** \brief see smt::farkas_util::set_split_literals */
    void set_split_literals (bool v) {m_split_literals = v;}

};


}

#endif
