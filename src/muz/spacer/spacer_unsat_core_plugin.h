#ifndef _SPACER_UNSAT_CORE_PLUGIN_H_
#define _SPACER_UNSAT_CORE_PLUGIN_H_

#include "ast.h"

namespace spacer {
    
class unsat_core_learner;
class unsat_core_plugin {
    
public:
    unsat_core_plugin(unsat_core_learner& learner) : m_learner(learner){};
    virtual ~unsat_core_plugin();
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
    unsat_core_plugin_farkas_lemma(unsat_core_learner& learner, bool split_literals, bool use_constant_from_a=true) : unsat_core_plugin(learner), m_split_literals(split_literals), m_use_constant_from_a(use_constant_from_a) {};
    
    virtual void compute_partial_core(proof* step) override;
    
private:
    bool m_split_literals;
    bool m_use_constant_from_a;
    /*
     * compute linear combination of literals 'literals' having coefficients 'coefficients' and save result in res
     */
    void compute_linear_combination(const vector<rational>& coefficients, const ptr_vector<app>& literals, expr_ref& res);
};

}
#endif
