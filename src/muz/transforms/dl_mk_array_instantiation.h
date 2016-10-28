/*++

Module Name:

    dl_mk_array_instantiation.h

Abstract:
    Transforms predicates so that array invariants can be discovered.
    
    Motivation   :  Given a predicate P(a), no quantifier-free solution can express that P(a) <=> forall i, P(a[i]) = 0

    Solution     :  We introduce a fresh variable i, and transform P(a) into P#(i, a). Thus, discovering that P#(i,a) <=> a[i] = 0, 
                    is equivalent to discovering forall i, P(a[i]) = 0.
                    The impact on Horn rules is the following :
                    Let us take a Horn rule : P(a, args) /\ phi(a, args, args') => P'(args') (for simplicity, assume there are no arrays in args').
                    We do not only transform it into P#(i, a, args) /\ phi(a, args, args') => P'(args'), doing so would allow phi only to read 
                    from one chosen cell i. Instead, we transform it into  (/\_r in read_indices(phi) P#(r, a, args)) /\ phi(a, args, args') => P'(args').
                    


    Limitations  :  This technique can only discover invariants on arrays that depend on one quantifier.
    Related work :  Techniques relying on adding quantifiers and eliminating them. See dl_mk_quantifier_abstraction and dl_mk_quantifier_instantiation

Implementation:
    The implementation follows the solution suggested above, with more options. The addition of options implies that in the simple
    case described above, we in fact have P(a) transformed into P(i, a[i], a).

    1) Dealing with multiple arrays -> Currently, we add one quantifier per array. An improvement of this technique would be to allow
       the user to chose how many quantifiers per type and how many quantifiers per array.

    2) Inforcing the instantiation -> We suggest an option (enforce_instantiation) to enforce this abstraction. This transforms
       P(a) into P(i, a[i]). This enforces the solver to limit the space search at the cost of imprecise results.

    3) Adding slices in the mix -> We wish to have the possibility to further restrict the search space: we want to smash cells, given a smashing rule.
       For example, in for loops j=0; j<n; j++, it might be relevant to restrict the search space and look for invariants that only depend on whether i,
       the quantified variable, is between [0,j[ or ]j, +oo[.
       This means we are given a function GetId : Index -> SetIds, that given an index, returns its id. In our example, GetId(i) could be
       ite(i<j, true, false).
       Given that GetId function, P(a) /\ phi(a, ...) => P'(...) is transformed into 
       (/\_r in read_indices(phi) P(id_r, a[r], a) /\ GetId(r) = id_r) /\ phi(a, ...) => P'(...).

    4) Reducing the set of r in read_indices(phi): in fact, we do not need to "instantiate" on all read indices of phi, 
       we can restrict ourselves to those "linked" to a, through equalities and stores.


Author:

    Julien Braine

Revision History:   

--*/

#ifndef DL_MK_ARRAY_INSTANTIATION_H_
#define DL_MK_ARRAY_INSTANTIATION_H_


#include "dl_rule_transformer.h"

namespace datalog {

    class context;
    class mk_array_instantiation : public rule_transformer::plugin {
        //Context objects
        ast_manager&      m;
        context&          m_ctx;
        array_util   m_a;

     public:
        mk_array_instantiation(context & ctx, unsigned priority);
        rule_set * operator()(rule_set const & source);
        virtual ~mk_array_instantiation(){}
    };



};

#endif /* DL_MK_ARRAY_INSTANTIATION_H_ */

