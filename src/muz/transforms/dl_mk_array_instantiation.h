/*++

Module Name:

    dl_mk_array_instantiation.h

Abstract:
    Transforms predicates so that array invariants can be discovered.
    
    Motivation   :  Given a predicate P(a), no quantifier-free solution can express that P(a) <=> forall i, P(a[i]) = 0

    Solution     :  Introduce a fresh variable i, and transform P(a) into P!inst(i, a). 
                    Now, (P!inst(i,a) := a[i] = 0) <=> P(a) := forall i, a[i] = 0.

                    Transformation on Horn rules:
                    P(a, args) /\ phi(a, args, args') => P'(args') (for simplicity, assume there are no arrays in args').
                    Is transformed into:
                    (/\_r in read_indices(phi) P!inst(r, a, args)) /\ phi(a, args, args') => P'(args')
                    
    Limitations  :  This technique can only discover invariants on arrays that depend on one quantifier.
    Related work :  Techniques relying on adding quantifiers and eliminating them. See dl_mk_quantifier_abstraction and dl_mk_quantifier_instantiation

Implementation:
    The implementation follows the solution suggested above, with more options. The addition of options implies that in the simple
    case described above, we in fact have P(a) transformed into P(i, a[i], a).

    1) Dealing with multiple arrays -> Currently, we add one quantifier per array. An improvement of this technique would be to allow
       the user to chose how many quantifiers per type and how many quantifiers per array. These options correspond to the parameters
       fixedpoint.xform.instantiate_arrays.nb_per_type and fixedpoint.xform.instantiate_arrays.nb_per_array.

    2) Inforcing the instantiation -> We suggest an option (enforce_instantiation) to enforce this abstraction. This transforms
       P(a) into P(i, a[i]). This enforces the solver to limit the space search at the cost of imprecise results. This option
       corresponds to fixedpoint.xform.instantiate_arrays.enforce

    3) Adding slices in the mix -> We wish to have the possibility to further restrict the search space: we want to smash cells, given a smashing rule.
       For example, in for loops j=0; j<n; j++, it might be relevant to restrict the search space and look for invariants that only depend on whether 
       0<=i<j or j<=i, where i is the quantified variable.

       Formally, a smashing rule is a function from the Index set (usually integer) to integers (the id set). 
       GetId(i) should return the id of the set i belongs in.
       
       In our example, we can give 0 as the id of the set {n, 0<=n<j} and 1 for the set {n, j<=n}, and -1 for the set {n, n<0}. We then have
       GetId(i) = ite(i<0, -1, ite(i<j, 0, 1))

       Given that GetId function, P(a) /\ phi(a, ...) => P'(...) is transformed into 
       (/\_r in read_indices(phi) P(id_r, a[r], a) /\ GetId(r) = id_r) /\ phi(a, ...) => P'(...).
       Note : when no slicing is done, GetId(i) = i.
       This option corresponds to fixedpoint.xform.instantiate_arrays.slice_technique

       Although we described GetId as returning integers, there is no reason to restrict the type of ids to integers. A more direct method, 
       for the 0<=i<j or j<=i case could be :
       GetId(i) = (i<0, i<j)

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
       
       app_ref get_select(unsigned nb_indices, expr* const* args);

       //Function to return the new predicate and the corresponding map for dynamic programming.
       app_ref get_new_predicate(const expr_ref_vector& indices, const app_ref& old_predicate);

       
     protected:
        virtual expr_ref_vector getId(const expr_ref_vector& select_args, const app_ref& old_pred);
     public:
        mk_array_instantiation(context & ctx, unsigned priority);
        rule_set * operator()(rule_set const & source);
        virtual ~mk_array_instantiation(){}
    };



};

#endif /* DL_MK_ARRAY_INSTANTIATION_H_ */
