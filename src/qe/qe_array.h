/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    qe_array.h

Abstract:

    Quantifier Elimination for Arrays

Author:

    Anvesh Komuravelli (t-anvko) 2013-08-29.

Revision History:

--*/
#ifndef __QE_ARRAY_H__
#define __QE_ARRAY_H__

#include "ast.h"
#include "array_decl_plugin.h"
#include "arith_decl_plugin.h"
#include "params.h"
#include "expr_substitution.h"
#include "expr_map.h"
#include "th_rewriter.h"
#include "qe_util.h"
#include "qe.h"

class tactic;

bool is_partial_eq (app* a);

/**
 * \brief utility class for partial equalities
 *
 * A partial equality (a ==I b), for two arrays a,b and a finite set of indices I holds
 *   iff (Forall i. i \not\in I => a[i] == b[i]); in other words, it is a
 *   restricted form of the extensionality axiom
 *
 * using this class, we denote (a =I b) as f(a,b,i0,i1,...)
 *   where f is an uninterpreted predicate with name PARTIAL_EQ and
 *   I = {i0,i1,...}
 */
class peq {
    ast_manager&        m;
    expr_ref            m_lhs;
    expr_ref            m_rhs;
    unsigned            m_num_indices;
    expr_ref_vector     m_diff_indices;
    func_decl_ref       m_decl;     // the partial equality declaration
    app_ref             m_peq;      // partial equality application
    app_ref             m_eq;       // equivalent std equality using def. of partial eq
    array_util          m_arr_u;
    ast_eq_proc         m_eq_proc;  // for checking if two asts are equal

public:
    static const char* PARTIAL_EQ;

    peq (app* p, ast_manager& m);

    peq (expr* lhs, expr* rhs, unsigned num_indices, expr * const * diff_indices, ast_manager& m);

    void lhs (expr_ref& result);

    void rhs (expr_ref& result);

    void get_diff_indices (expr_ref_vector& result);

    void mk_peq (app_ref& result);

    void mk_eq (app_ref_vector& aux_consts, app_ref& result, bool stores_on_rhs = true);
};

class qe_array {

    ast_manager&                m;
    array_util                  m_arr_u;
    arith_util                  m_ari_u;
    expr_map                    m_elim_stores_cache;
    ast_mark                    m_elim_stores_done;
    ast_mark                    m_has_stores;
    expr_ref_vector             _tmps;      // tmp storage to ensure non-zero ref count

    app_ref_vector              m_aux_consts;
    ast_eq_proc                 m_eq_proc;  // for checking if two asts are equal
    bool                        m_cancel;   // tactic thingy

    th_rewriter                 m_rw;       // to apply cheap simplifications
    is_variable_test*           m_is_var;   // for filtering variables to eliminate from others

    // checks if e is marked by m_elim_stores_done or m_has_stores
    // and adds to _tmp otherwise;
    // then, it's marked by am (which is one of m_elim_stores_done and
    // m_has_stores)
    void ensure_ref_and_mark (expr* e, ast_mark& am);

    void reset ();

    void init ();

    bool is_variable (expr* e);

    /**
     * \brief convert stores into partial equalities and selects
     */
    void elim_stores (expr* e, expr_ref& result, expr_ref_vector& partial_eqs);

    /**
     * \brief eliminate disequality between array types using extensionality
     */
    void elim_disequality (expr* arr0, expr* arr1, expr_ref& result);

    /**
     * \brief process the select expression to eliminate stores or to cofactor
     * out ite terms
     */
    void select (app* a, expr_ref& result, expr_ref_vector& partial_eqs);

    /**
     * \brief process the partial equality expression to eliminate stores or to
     * cofactor out ite terms
     */
    void partial_equality (app* e, expr_ref& result, expr_ref_vector& partial_eqs);

    /**
     * \brief eliminate partial eqs on var_idx (from old_partial_eqs) by case
     * splitting and substitution; new_partial_eqs contains all the partial eqs
     * of the result
     */
    void elim_partial_eqs (expr* e, unsigned var_idx, expr_ref_vector const& old_partial_eqs, expr_ref& result, expr_ref_vector& new_partial_eqs);

    /**
     * \brief replace selects on var_idx with fresh constants
     *
     * sel_cache is used internally to cache results;
     * sel_exps contains the replaced select terms;
     * sel_consts are the newly created constants;
     */
    void elim_selects (expr* e, unsigned var_idx, expr_map& sel_cache, expr_ref_vector& sel_exps, expr_ref_vector& sel_consts, expr_ref& result);

    /**
     * \brief Ackermann reduction; sel_exps are mapped to sel_consts
     */
    void generate_congruences (expr_ref_vector const& sel_exps,
                               expr_ref_vector const& sel_consts,
                               expr_ref_vector& result);

    /**
     * \brief eliminate given array variables from Exists (var_idx, e) by possibly
     * introducing new quantified variables of the index/value sorts of the
     * array variables
     *
     * let 'a' be an arbitrary array variable being eliminated
     *
     * assume that stores "on a" or "of a" are not used as index terms
     * [ e.g. of a store "on a" -- Store (a,i,x)
     *   e.g. of a store "of a" -- Store (b,i,a) ]
     *
     * assume no uninterpreted functions with 'a' as a subterm (e.g. disallow
     * subexpressions such as f(a)) -- effectively, the only operations allowed
     * on 'a' are selects, stores, equalities and disequalities.
     *
     *
     *
     * Step 1: convert all stores into partial equalities and selects, using
     *
     *      Select-after-store: L(Store(a,i,x)[j]) --> L(ite(i==j, x, a[j]))
     *
     *      Partial equality: (cf. Stump et al. "A decision procedure for an
     *                         extensional theory of arrays", LICS 2001)
     *          (Store(a,i,x) ==I b) --> And (i \in I => (a ==I b),
     *                                        i \not\in I => And (a ==I+i b, b[i] == x))
     *
     *      Extensionality:
     *          Not (a==b) --> Not (a[i] == b[i]),
     *              where i is fresh
     *
     * Step 2: eliminate partial equalities
     *
     *      case split on each partial equality being true or false and use
     *      substitution based on the following transformation
     *
     *      Partial-equality-to-equality:
     *          (a ==I b) --> (a == Store (b, {i1,...,in} <- {x1,...,xn})
     *              where I = {i1,...,in} and x1,...,xn are fresh
     *
     * Step 3: eliminate selects
     *
     *      use Ackermann reduction
     */
    void qe_array_core (expr* e, uint_set const& var_idx, expr_ref& result);

public:

    qe_array (ast_manager& mgr);

    virtual ~qe_array () { dealloc (m_is_var); }

    /**
     * \brief
     *
     * for now, assume that there is at most one exists-quantifier block for an array;
     * eliminates only the array variables and leaves others untouched;
     * depending on the input formula, new existentially quantified variables of
     * the index/value sorts may be introduced
     *
     * it can be extended to universals by simply negating the matrix and negating the
     * result back.
     *
     * it can also be extended to more than one quantifier block, by an
     * inside-out quantifier elimination, provided all quantifiers in each block
     * can be eliminated. if all the quantified variables are arrays (satisfying
     * the assumption that arrays are not used as indices in selects), then this
     * can be done using qe-array. if there are quantified variables from other
     * theories (rationals, integers, etc.) we need to invoke their qe, or leave
     * them quantified and give up!
     */
    void operator () (expr* fml, expr_ref& result);

    /**
     * \brief
     * existentially eliminate free variables with indices var_idx;
     * assume that the vars at the given indices are of array type;
     * num_vars is the number of variables already in fml
     */
    void operator () (uint_set var_idx, expr_ref& fml, unsigned num_vars);

    // tactic thingy
    void set_cancel (bool flag) { m_cancel = flag; }
};

tactic * mk_qe_array_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("qe-array", "apply existential qe for arrays", "mk_qe_array_tactic(m, p)")
*/

#endif
