/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    qe_array.cpp

Abstract:

    Quantifier Elimination for Arrays

Author:

    Anvesh Komuravelli (t-anvko) 2013-08-29.

Revision History:

--*/
#include "qe_array.h"
#include "tactic.h"
#include "cooperate.h"
#include "var_subst.h"
#include "expr_replacer.h"
#include "ast_pp.h"
#include "expr_substitution.h"
#include "expr_abstract.h"
#include "quant_hoist.h"



// peq

const char* peq::PARTIAL_EQ = "partial_eq";

peq::peq (app* p, ast_manager& m):
    m (m),
    m_lhs (p->get_arg (0), m),
    m_rhs (p->get_arg (1), m),
    m_num_indices (p->get_num_args ()-2),
    m_diff_indices (m),
    m_decl (p->get_decl (), m),
    m_peq (p, m),
    m_eq (m),
    m_arr_u (m)
{
    SASSERT (is_partial_eq (p));
    SASSERT (m_arr_u.is_array (m_lhs) &&
             m_arr_u.is_array (m_rhs) &&
             m_eq_proc (m.get_sort (m_lhs), m.get_sort (m_rhs)));
    for (unsigned i = 2; i < p->get_num_args (); i++) {
        m_diff_indices.push_back (p->get_arg (i));
    }
}

peq::peq (expr* lhs, expr* rhs, unsigned num_indices, expr * const * diff_indices, ast_manager& m):
    m (m),
    m_lhs (lhs, m),
    m_rhs (rhs, m),
    m_num_indices (num_indices),
    m_diff_indices (m),
    m_decl (m),
    m_peq (m),
    m_eq (m),
    m_arr_u (m)
{
    SASSERT (m_arr_u.is_array (lhs) &&
             m_arr_u.is_array (rhs) &&
             m_eq_proc (m.get_sort (lhs), m.get_sort (rhs)));
    ptr_vector<sort> sorts;
    sorts.push_back (m.get_sort (m_lhs));
    sorts.push_back (m.get_sort (m_rhs));
    for (unsigned i = 0; i < num_indices; i++) {
        sorts.push_back (m.get_sort (diff_indices [i]));
        m_diff_indices.push_back (diff_indices [i]);
    }
    m_decl = m.mk_func_decl (symbol (PARTIAL_EQ), sorts.size (), sorts.c_ptr (), m.mk_bool_sort ());
}

void peq::lhs (expr_ref& result) { result = m_lhs; }

void peq::rhs (expr_ref& result) { result = m_rhs; }

void peq::get_diff_indices (expr_ref_vector& result) {
    for (unsigned i = 0; i < m_diff_indices.size (); i++) {
        result.push_back (m_diff_indices.get (i));
    }
}

void peq::mk_peq (app_ref& result) {
    if (!m_peq) {
        ptr_vector<expr> args;
        args.push_back (m_lhs);
        args.push_back (m_rhs);
        for (unsigned i = 0; i < m_num_indices; i++) {
            args.push_back (m_diff_indices.get (i));
        }
        m_peq = m.mk_app (m_decl, args.size (), args.c_ptr ());
    }
    result = m_peq;
}

void peq::mk_eq (app_ref_vector& aux_consts, app_ref& result, bool stores_on_rhs) {
    if (!m_eq) {
        expr_ref lhs (m_lhs, m), rhs (m_rhs, m);
        if (!stores_on_rhs) {
            std::swap (lhs, rhs);
        }
        // lhs = (...(store (store rhs i0 v0) i1 v1)...)
        sort* val_sort = get_array_range (m.get_sort (lhs));
        expr_ref_vector::iterator end = m_diff_indices.end ();
        for (expr_ref_vector::iterator it = m_diff_indices.begin ();
                it != end; it++) {
            app* val = m.mk_fresh_const ("diff", val_sort);
            ptr_vector<expr> store_args;
            store_args.push_back (rhs);
            store_args.push_back (*it);
            store_args.push_back (val);
            rhs = m_arr_u.mk_store (store_args.size (), store_args.c_ptr ());
            aux_consts.push_back (val);
        }
        m_eq = m.mk_eq (lhs, rhs);
    }
    result = m_eq;
}


bool is_partial_eq (app* a) {
    return a->get_decl ()->get_name () == peq::PARTIAL_EQ;
}



// qe_array



qe_array::qe_array (ast_manager& mgr):
    m (mgr),
    m_arr_u (m),
    m_ari_u (m),
    m_elim_stores_cache (m),
    _tmps (m),
    m_aux_consts (m),
    m_cancel (false),
    m_rw (m),
    m_is_var (0)
{}

void qe_array::ensure_ref_and_mark (expr* e, ast_mark& am) {
    if (!m_elim_stores_done.is_marked (e) && !m_has_stores.is_marked (e)) {
        _tmps.push_back (e);
    }
    am.mark (e, true);
}

void qe_array::reset () {
    m_elim_stores_cache.reset ();
    m_elim_stores_done.reset ();
    m_has_stores.reset ();
    m_aux_consts.reset ();
    _tmps.reset ();
    m_cancel = false;
    dealloc (m_is_var);
    m_is_var = 0;
}

void qe_array::init () { reset (); }

bool qe_array::is_variable (expr* e) {
    SASSERT (m_is_var);
    return (*m_is_var) (e);
}

void qe_array::qe_array_core (expr* e, uint_set const& var_idx, expr_ref& result) {
    expr_ref_vector partial_eqs_1 (m), partial_eqs_2 (m);
    expr_ref tmp (m);

    // convert all stores into partial equalities
    elim_stores (e, tmp, partial_eqs_1);
    // TODO: push negations inside to get rid off unnecessary partial equalities
    //
    //   !(a ==I b) --> (idx \not\in I /\ a[idx] != b[idx]) where idx is fresh
    //
    // this step is not necessary
    TRACE ("qe_array",
            tout << "Eliminated stores" << mk_pp (tmp, m) << "\n";
            tout << "Remaining partial equalities:\n";
            for (unsigned i = 0; i < partial_eqs_1.size (); i++) {
                tout << "peq: " << mk_pp (partial_eqs_1.get (i), m) << "\n";
            }
          );

    uint_set::iterator end = var_idx.end ();

    // eliminate partial equalities of the array variables, one by one
    expr_ref_vector *peqs_curr = &partial_eqs_1;
    expr_ref_vector *peqs_new = &partial_eqs_2;
    for (uint_set::iterator it = var_idx.begin (); it != end; it++) {
        peqs_new->reset ();
        elim_partial_eqs (tmp, *it, *peqs_curr, tmp, *peqs_new);
        TRACE ("qe_array",
                tout << "Eliminated partial eqs on var idx " << *it << "\n";
                tout << "Remaining partial equalities:\n";
                for (unsigned i = 0; i < peqs_new->size (); i++) {
                    tout << "peq: " << mk_pp (peqs_new->get (i), m) << "\n";
                }
              );
        std::swap (peqs_new, peqs_curr);
    }
    // eliminate any remaining partial equalities on arrays we aren't eliminating
    // TODO: maybe we can be more eager and not generate these in the first place
    if (!peqs_curr->empty ()) {
        expr_substitution sub (m);
        proof_ref pr (m.mk_asserted (m.mk_true ()), m);
        for (unsigned i = 0; i < peqs_curr->size (); i++) {
            // turn into an equality
            SASSERT (is_partial_eq (to_app (peqs_curr->get (i))));
            peq p (to_app (peqs_curr->get (i)), m);
            app_ref eq (m);
            p.mk_eq (m_aux_consts, eq);
            sub.insert (peqs_curr->get (i), eq, pr);
            TRACE ("qe_array",
                    tout << "Eliminating extra peq: " << mk_pp (peqs_curr->get (i), m) << " with " << mk_pp (eq, m) << "\n";
                  );
        }
        scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer (m);
        rep->set_substitution (&sub);
        (*rep) (tmp);
    }

    // eliminate selects on the array variables by Ackermann reduction, one by one
    for (uint_set::iterator it = var_idx.begin (); it != end; it++) {
        // replace selects on *it by new constants
        expr_map sel_cache (m);
        expr_ref_vector sel_exps (m);
        expr_ref_vector sel_consts (m);
        elim_selects (tmp, *it, sel_cache, sel_exps, sel_consts, tmp);
        SASSERT (sel_consts.size () == sel_exps.size ());
        TRACE ("qe_array",
                tout << "Fresh consts for select expressions" << "\n";
                for (unsigned i = 0; i < sel_consts.size (); i++) {
                    tout << mk_pp (sel_exps.get (i), m) << "  " << mk_pp (sel_consts.get (i), m) << "\n";
                }
              );
        // generate congruences
        expr_ref_vector congruences (m);
        generate_congruences (sel_exps, sel_consts, congruences);
        TRACE ("qe_array",
                tout << "Generated congruences:\n";
                for (unsigned i = 0; i < congruences.size (); i++) {
                    tout << mk_pp (congruences.get (i), m) << "\n";
                }
              );
        // update
        tmp = m.mk_and (tmp,
                        m.mk_and (congruences.size (), congruences.c_ptr ()));
    }

    // simplify
    m_rw (tmp, tmp);

    // mk result
    result = tmp;

    TRACE ("qe_array",
            tout << "Final Matrix:\n" << mk_pp (result, m) << "\n";
          );
}

void qe_array::operator () (expr* fml, expr_ref& result) {
    if (!has_quantifiers (fml)) {
        result = fml;
        return;
    }

    init ();

    expr_ref exp_body (m);
    quantifier_hoister qh (m);

    ptr_vector<sort> qvar_sorts;
    svector<symbol> qvar_names;
    exp_body = fml;
    qh.pull_quantifier (false, exp_body, &qvar_sorts, &qvar_names, false, false);

    // find indices to eliminate and replace the rest by constants
    app_ref_vector non_arrays (m);
    uint_set var_idx_to_elim;
    expr_substitution sub (m);
    proof_ref pr (m.mk_asserted (m.mk_true ()), m);
    unsigned num = qvar_sorts.size ();
    for (unsigned i = 0; i < num; i++) {
        unsigned idx = num-i-1;
        sort* s = qvar_sorts.get (i);
        symbol const& sym = qvar_names.get (i);
        app_ref c (m.mk_const (sym, s), m);
        if (m_arr_u.is_array (c)) {
            var_idx_to_elim.insert (idx);
        }
        else {
            sort* s = get_sort (c);
            var_ref v (m.mk_var (idx, s), m);
            sub.insert (v, c, pr);
            non_arrays.push_back (c);
        }
    }
    if (var_idx_to_elim.empty ()) {
        // no array variables
        result = fml;
        return;
    }

    m_is_var = alloc (is_variable_test, var_idx_to_elim, true);

    // substitute constants for all variables we don't eliminate
    scoped_ptr<expr_replacer> rep = mk_default_expr_replacer (m);
    rep->set_substitution (&sub);
    (*rep) (exp_body);

    // eliminate array variables
    qe_array_core (exp_body, var_idx_to_elim, exp_body);

    // existentially quantify non_arrays and m_aux_consts
    app_ref_vector qvars (m);
    qvars.append (non_arrays);
    qvars.append (m_aux_consts);
    result = exp_body;
    if (!qvars.empty ()) {
        qe::mk_exists (qvars.size (), qvars.c_ptr (), result);
    }
}

void qe_array::operator () (uint_set var_idx, expr_ref& fml, unsigned num_vars) {
    if (var_idx.empty ()) {
        return;
    }

    init ();
    m_is_var = alloc (is_variable_test, var_idx, true);
    // eliminate array variables
    qe_array_core (fml, var_idx, fml);
    // replace aux consts by variables; new variable indices should be >= num_vars
    expr_abstract (m, num_vars, m_aux_consts.size (), (expr* const*) m_aux_consts.c_ptr (), fml, fml);
}

void qe_array::elim_stores (expr* e, expr_ref& result, expr_ref_vector& partial_eqs) {
    if (!is_app (e)) {
        ensure_ref_and_mark (e, m_elim_stores_done);
        result = e;
        return;
    }

    if (m_elim_stores_done.is_marked (e)) {
        expr* e_new = 0; proof* pr;
        m_elim_stores_cache.get (e, e_new, pr);
        if (e_new) {
            result = e_new;
        } else {
            result = e;
        }
        return;
    }

    TRACE ("qe_array",
            tout << "Before elim stores: " << mk_pp (e, m) << "\n";
          );

    app_ref a (to_app (e), m);

    bool is_disequality = false;

    // detect if it is a disequality between arrays and use extensionality
    // NOTE: this is like an optimization to get rid off an unnecessary partial
    // equality and not a necessary step
    if (m.is_not (a) && a->get_num_args () == 1) {
        // check if it is an equality between arrays
        expr* arg = a->get_arg (0);
        if (m.is_eq (arg) && m_arr_u.is_array (to_app (arg)->get_arg (0))) {
            SASSERT (m_arr_u.is_array (to_app (arg)->get_arg (1)));
            is_disequality = true;
            // process disequality between arrays
            elim_disequality (to_app (arg)->get_arg (0), to_app (arg)->get_arg (1), result);
            elim_stores (result, result, partial_eqs);
        }
    }

    if (!is_disequality) {
        // process arguments
        expr_ref_vector args (m);
        bool args_have_stores = false;
        for (unsigned i = 0; i < a->get_num_args (); i++) {
            expr_ref arg (a->get_arg (i), m);
            elim_stores (arg.get (), arg, partial_eqs);
            args.push_back (arg);
            // does arg have stores?
            if (!args_have_stores && m_has_stores.is_marked (arg)) args_have_stores = true;
        }
        // update with new args
        app_ref a_new (m.mk_app (a->get_decl (), args.size (), args.c_ptr ()), m);
        result = a_new; // tentative

        TRACE ("qe_array",
                tout << "After processing arguments\n" << mk_pp (a_new, m) << "\n";
              );

        // mark if there are stores on a variable being eliminated
        if (args_have_stores) ensure_ref_and_mark (a_new, m_has_stores);
        else if (m_arr_u.is_store (a_new)) {
            expr* arr = a_new->get_arg (0);
            expr* val = a_new->get_arg (2);
            if (is_variable (arr) || is_variable (val)) { // storing 'on a' or 'of a'
                ensure_ref_and_mark (a_new, m_has_stores);
            }
        }

        if (m_arr_u.is_select (a_new)) {
            select (a_new, result, partial_eqs);
        } else if (is_partial_eq (a_new)) {
            partial_equality (a_new, result, partial_eqs);
        } else if (m.is_eq (a_new) && m_arr_u.is_array (a_new->get_arg (0))) {
            // equality between arrays, use partial equality rules
            SASSERT (m_arr_u.is_array (a_new->get_arg (1)));
            app_ref a_peq (m);
            peq p (a_new->get_arg (0), a_new->get_arg (1), 0, 0, m); p.mk_peq (a_peq);
            if (m_has_stores.is_marked (a_new))
                ensure_ref_and_mark (a_peq, m_has_stores);
            partial_equality (a_peq.get (), result, partial_eqs);
        }
    }

    if (!m_eq_proc (e, result)) {
        m_elim_stores_cache.insert (e, result, 0);
        ensure_ref_and_mark (result, m_elim_stores_done);
    }
    ensure_ref_and_mark (e, m_elim_stores_done);

    TRACE ("qe_array",
            tout << "After elim stores: " << mk_pp (result.get (), m) << "\n";
          );
}

void qe_array::elim_disequality (expr* arr0, expr* arr1, expr_ref& result) {

    // Not (arr0==arr1) --> Not (arr0[idx] == arr1[idx]), idx is fresh

    SASSERT (m_arr_u.is_array (arr0) && m_arr_u.is_array (arr1));

    sort* idx_sort = get_array_domain (get_sort (arr0), 0);
    app* idx = m.mk_fresh_const ("idx", idx_sort);
    m_aux_consts.push_back (idx);

    // arr0[idx]
    ptr_vector<expr> sel_args;
    sel_args.push_back (arr0);
    sel_args.push_back (idx);
    expr* arr0_idx = m_arr_u.mk_select (sel_args.size (), sel_args.c_ptr ());

    // arr1[idx]
    sel_args.set (0, arr1);
    expr* arr1_idx = m_arr_u.mk_select (sel_args.size (), sel_args.c_ptr ());

    TRACE ("qe_array",
            tout << "Transformed disequality is b/w " << mk_pp (arr0_idx, m)
                 << " and " << mk_pp (arr1_idx, m) << "\n";
          );

    result = m.mk_not (m.mk_eq (arr0_idx, arr1_idx));
    // elim stores from arr0[idx]!=arr1[idx]
    //app_ref a (m.mk_not (m.mk_eq (arr0_idx, arr1_idx)), m);
    //elim_stores (a, result, partial_eqs);
}

void qe_array::select (app* a, expr_ref& result, expr_ref_vector& partial_eqs) {
    SASSERT (m_arr_u.is_select (a));

    expr* arr = a->get_arg (0);
    expr* j = a->get_arg (1);

    if (m.is_ite (arr)) {

        // use cofactoring to move ite up one level
        //   ite (c, th, el) [j] --> ite (c, th[j], el[j])
        app* a_arr = to_app (arr);
        expr* c = a_arr->get_arg (0);
        expr* th = a_arr->get_arg (1);
        expr* el = a_arr->get_arg (2);
        // th[j]
        ptr_vector<expr> sel_args;
        sel_args.push_back (th);
        sel_args.push_back (j);
        app* th_j = m_arr_u.mk_select (sel_args.size (), sel_args.c_ptr ());
        // el[j]
        sel_args.set (0, el);
        app* el_j = m_arr_u.mk_select (sel_args.size (), sel_args.c_ptr ());
        // mk new a
        app_ref a_new (m.mk_ite (c, th_j, el_j), m);

        TRACE ("qe_array",
                tout << "Transformed select term: " << mk_pp (a_new, m) << "\n";
              );

        // elim stores from new a
        elim_stores (a_new, result, partial_eqs);

    } else if (m.is_ite (j)) {

        // use cofactoring to move ite up one level
        //   arr [ite (c, th, el)] --> ite (c, arr[th], arr[el])
        app* a_j = to_app (j);
        expr* c = a_j->get_arg (0);
        expr* th = a_j->get_arg (1);
        expr* el = a_j->get_arg (2);
        // arr[th]
        ptr_vector<expr> sel_args;
        sel_args.push_back (arr);
        sel_args.push_back (th);
        app* arr_th = m_arr_u.mk_select (sel_args.size (), sel_args.c_ptr ());
        // arr[el]
        sel_args.set (1, el);
        app* arr_el = m_arr_u.mk_select (sel_args.size (), sel_args.c_ptr ());
        // mk new a
        app_ref a_new (m.mk_ite (c, arr_th, arr_el), m);

        TRACE ("qe_array",
                tout << "Transformed select term: " << mk_pp (a_new, m) << "\n";
              );

        // elim stores from new a
        elim_stores (a_new, result, partial_eqs);

    } else if (m_has_stores.is_marked (a)) {

        // assuming no uninterpreted functions over arrays, and assuming that
        // index type is not an array type, stores can only be in the array part
        // of the select term, i.e. a select after a store

        SASSERT (m_arr_u.is_store (arr));

        app* store = to_app (arr);
        expr* j = a->get_arg (1);

        // Store(arr,i,x)[j]) --> If (i==j, x, arr[j])
        arr = store->get_arg (0);
        expr* i = store->get_arg (1);
        expr* x = store->get_arg (2);

        // check if i==j is statically known
        bool i_eq_j_known = m_eq_proc (i, j);

        if (i_eq_j_known) {
            TRACE ("qe_array",
                    tout << "Transformed select term: " << mk_pp (x, m) << "\n";
                  );
            result = x;
        } else {
            // i==j
            app* i_eq_j = m.mk_eq (i, j);

            // stores have already been eliminated from x

            // arr[j]
            ptr_vector<expr> sel_args;
            sel_args.push_back (arr);
            sel_args.push_back (j);
            app* arr_j = m_arr_u.mk_select (sel_args.size (), sel_args.c_ptr ());
            // mk new a
            app_ref a_new (m.mk_ite (i_eq_j, x, arr_j), m);

            TRACE ("qe_array",
                    tout << "Transformed select term: " << mk_pp (a_new, m) << "\n";
                  );

            // elim stores from new a
            elim_stores (a_new, result, partial_eqs);
        }

    } else { result = a; }
}

void qe_array::partial_equality (app* a, expr_ref& result, expr_ref_vector& partial_eqs) {

    // a is a partial equality
    SASSERT (is_partial_eq (a));

    // a =:= (lhs ==I rhs)
    peq p (a, m);
    expr_ref lhs (m), rhs (m);
    expr_ref_vector I (m);
    p.lhs (lhs);
    p.rhs (rhs);
    p.get_diff_indices (I);

    if (m.is_ite (lhs) || m.is_ite (rhs)) {

        // normalize ite's to the left
        if (m.is_ite (rhs)) {
            std::swap (lhs, rhs);
        }
        app* a_lhs = to_app (lhs);

        // use cofactoring to move ite up one level
        //  (ite (c, th, el) ==I rhs) --> (c => th ==I rhs) /\ (!c => el ==I rhs)
        expr* c = a_lhs->get_arg (0);
        expr* th = a_lhs->get_arg (1);
        expr* el = a_lhs->get_arg (2);

        // th ==I rhs
        peq p1 (th, rhs, I.size (), I.c_ptr (), m);
        app_ref th_peq (m);
        p1.mk_peq (th_peq);
        // el ==I rhs
        peq p2 (el, rhs, I.size (), I.c_ptr (), m);
        app_ref el_peq (m);
        p2.mk_peq (el_peq);

        // mk new a
        app* impl1 = m.mk_implies (c, th_peq);
        app* impl2 = m.mk_implies (m.mk_not (c), el_peq);
        app_ref a_new (m.mk_and (impl1, impl2), m);

        TRACE ("qe_array",
                tout << "Transformed partial equality: " << mk_pp (a_new, m) << "\n";
              );

        // elim stores from new a
        elim_stores (a_new, result, partial_eqs);

    } else if (m_has_stores.is_marked (a)) {

        // normalize stores to the left
        if (m_has_stores.is_marked (rhs)) {
            std::swap (lhs, rhs);
        }
        app* a_lhs = to_app (lhs);

        /** (Store(arr0,i,x) ==I arr1) -->
         *
         *  (i \in I => (arr0 ==I arr1)) /\
         *  (i \not\in I => (arr0 ==I+i arr1) /\ (arr1[i] == x)))
         */

        expr* arr0 = a_lhs->get_arg (0);
        expr* i = a_lhs->get_arg (1);
        expr* x = a_lhs->get_arg (2);
        expr* arr1 = rhs;

        // check if i \in I is statically known;
        // parallely build expression for (i \in I)
        bool i_in_I_known = false, i_not_in_I_known = false;
        app_ref i_in_I (m);
        if (I.size () == 0) {
            i_not_in_I_known = true;
            i_in_I = m.mk_false ();
        } else {
            expr_ref_vector disjs (m);
            expr_ref_vector::iterator end = I.end ();
            for (expr_ref_vector::iterator it = I.begin (); it != end; it++) {
                if (!i_in_I_known && m_eq_proc ((*it), i))
                    i_in_I_known = true;
                disjs.push_back (m.mk_eq (i, (*it)));
            }
            i_in_I = m.mk_or (disjs.size (), disjs.c_ptr ());
        }

        // arr0 ==I arr1
        peq p1 (arr0, arr1, I.size (), I.c_ptr (), m);
        app_ref th (m);
        p1.mk_peq (th);

        // arr0 ==I+i arr1
        I.push_back (i);
        peq p2 (arr0, arr1, I.size (), I.c_ptr (), m);
        app_ref peq2 (m);
        p2.mk_peq (peq2);

        // arr1[i] == x
        ptr_vector<expr> sel_args;
        sel_args.push_back (arr1);
        sel_args.push_back (i);
        expr* sel = m_arr_u.mk_select (sel_args.size (), sel_args.c_ptr ());
        expr_ref updt_eq (m.mk_eq (sel, x), m);

        app_ref el (m.mk_and (peq2, updt_eq), m);

        app_ref a_new (m);

        if (i_in_I_known) {
            // th (viz. arr0 ==I arr1) is the new a
            a_new = th;
        } else if (i_not_in_I_known) {
            // el (viz. (arr0 ==I+i arr1) /\ (arr1[i] == x))
            //   is the new a
            a_new = el;
        } else {
            // mk new a
            app* impl1 = m.mk_implies (i_in_I, th);
            app* impl2 = m.mk_implies (m.mk_not (i_in_I), el);
            a_new = m.mk_and (impl1, impl2);
        }

        TRACE ("qe_array",
                tout << "Transformed partial equality: " << mk_pp (a_new, m) << "\n";
              );

        // elim stores from new a
        elim_stores (a_new, result, partial_eqs);

    } else {

        if (m_eq_proc (lhs, rhs)) {
            // (a ==I a) == True
            result = m.mk_true ();
        } else {
            result = a;
            partial_eqs.push_back (a);
            TRACE ("qe_array",
                    tout << "Basic partial equality: " << mk_pp (a, m) << "\n";
                  );
        }

    }
}

void qe_array::elim_selects (expr* e, unsigned var_idx, expr_map& sel_cache, expr_ref_vector& sel_exps, expr_ref_vector& sel_consts, expr_ref& result) {
    if (!is_app (e)) {
        result = e;
        return;
    }

    expr* e_new = 0; proof* pr;
    sel_cache.get (e, e_new, pr);
    if (e_new) {
        result = e_new;
        return;
    }

    app_ref a (to_app (e), m);
    if (m_arr_u.is_select (a) && m_arr_u.is_const (a->get_arg (0))) {
        // (K x)[y] evaluates to x irrespective of y
        result = (to_app (a->get_arg (0)))->get_arg (0);
    } else {
        expr_ref_vector args (m);
        for (unsigned i = 0; i < a->get_num_args (); i++) {
            expr_ref arg (a->get_arg (i), m);
            elim_selects (arg, var_idx, sel_cache, sel_exps, sel_consts, arg);
            args.push_back (arg);
        }
        app* a_new = m.mk_app (a->get_decl (), args.size (), args.c_ptr ());
        result = a_new; // tentative

        if (m_arr_u.is_select (a_new)) {
            expr* arr = a_new->get_arg (0);
            if (is_variable (arr) && to_var (arr)->get_idx () == var_idx) {
                // what I am looking for; replace the select with a new constant
                sort* val_sort = get_array_range (m.get_sort (arr));
                app* val = m.mk_fresh_const ("sel", val_sort);
                sel_exps.push_back (a_new);
                sel_consts.push_back (val);
                m_aux_consts.push_back (val);
                result = val;
            }
        }
    }

    sel_cache.insert (e, result, 0);
}

void qe_array::elim_partial_eqs (expr* e, unsigned var_idx, expr_ref_vector const& old_partial_eqs, expr_ref& result, expr_ref_vector& new_partial_eqs) {

    expr_ref_vector result_disjs (m);

    expr_substitution sub (m);
    proof_ref pr (m.mk_asserted (m.mk_true ()), m);
    scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer (m);

    var_ref v (m);

    expr_ref_vector::iterator end = old_partial_eqs.end ();
    for (expr_ref_vector::iterator it = old_partial_eqs.begin ();
            it != end; it++) {
        // lhs ==I rhs
        app* a = to_app (*it);

        // obtain lhs and rhs
        peq p (a, m);
        expr_ref lhs (m), rhs (m);
        p.lhs (lhs); p.rhs (rhs);

        // check if it's a partial equality for the variable of interest
        if (is_variable (rhs) && to_var (rhs)->get_idx () == var_idx) {
            std::swap (lhs, rhs);
        } else if (!(is_variable (lhs) && to_var (lhs)->get_idx () == var_idx)) {
            // var_idx can only appear in a select term;
            // such equalities are going to remain;
            // (when we consider the case of all partial eqs on var_idx being false)
            new_partial_eqs.push_back (*it);
            continue;
        }

        TRACE ("qe_array",
                tout << "Processing partial equality: " << mk_pp (a, m) << "\n";
              );

        // v ==I rhs

        if (!v) {
            SASSERT (is_variable (lhs));
            v = to_var (lhs);
        }

        expr_ref_vector I (m);
        p.get_diff_indices (I);

        // ensure that the var to eliminate doesn't appear in rhs or I;
        // use fresh constants for reads on it
        expr_map sel_cache (m);
        expr_ref_vector sel_exps (m);
        expr_ref_vector sel_consts (m);
        expr_ref rhs_new (m);
        elim_selects (rhs, var_idx, sel_cache, sel_exps, sel_consts, rhs_new);
        expr_ref_vector I_new (m);
        expr_ref_vector::iterator I_end = I.end ();
        for (expr_ref_vector::iterator idx_it = I.begin (); idx_it != I_end; idx_it++) {
            expr_ref idx_new (m);
            elim_selects (*idx_it, var_idx, sel_cache, sel_exps, sel_consts, idx_new);
            I_new.push_back (idx_new);
        }

        // make equalities between selects and the newly introduced constants
        expr_ref_vector sel_const_eqs (m);
        SASSERT (sel_consts.size () == sel_exps.size ());
        for (unsigned i = 0; i < sel_consts.size (); i++) {
            sel_const_eqs.push_back (m.mk_eq (sel_consts.get (i), sel_exps.get (i)));
            TRACE ("qe_array",
                    tout << "Fresh const for select term: "
                         << mk_pp (sel_exps.get (i), m)
                         << mk_pp (sel_consts.get (i), m)
                         << "\n";
                  );
        }

        // turn the partial equality into an equality, using definition
        peq p_new (lhs, rhs_new, I_new.size (), I_new.c_ptr (), m);
        app_ref eq (m);
        p_new.mk_eq (m_aux_consts, eq);

        // case split on the current partial equality being true or false
        //   exists v. phi(v==x)
        //   <=>
        //   exists v. [v==x /\ phi(v==x/true)] \/ exists v. [v!=x /\ phi(v==x/false)]

        // true case
        sub.insert (a, m.mk_true (), pr);
        TRACE ("qe_array",
                tout << "Sub Pair: " << mk_pp (a, m) << " " << mk_pp (m.mk_true (), m) << "\n";
              );
        // use equality on v to substitute
        //   exists v. [v==x /\ phi(v==x/true)]
        //   <=>
        //   phi(v==x/true, v/x)
        sub.insert (eq->get_arg (0), eq->get_arg (1), pr);
        TRACE ("qe_array",
                tout << "Sub Pair: " << mk_pp (eq->get_arg (0), m) << " " << mk_pp (eq->get_arg (1), m) << "\n";
              );
        // substitute and simplify
        expr_ref disj (e, m);
        disj = m.mk_and (disj,
                         m.mk_and (sel_const_eqs.size (), sel_const_eqs.c_ptr ()));
        TRACE ("qe_array",
                tout << "Before sub:\n" << mk_pp (disj, m) << "\n";
              );
        rep->set_substitution (&sub);
        (*rep)(disj);
        TRACE ("qe_array",
                tout << "After sub:\n" << mk_pp (disj, m) << "\n";
              );
        expr_ref_vector partial_eqs (m);
        elim_stores (disj.get (), disj, partial_eqs);
        // add any newly generated partial eqs
        new_partial_eqs.append (partial_eqs);
        TRACE ("qe_array",
                tout << "After eliminating stores:\n" << mk_pp (disj, m) << "\n";
              );
        result_disjs.push_back (disj);

        // prepare for the false case;
        //
        // there are many possibilities for the next disjunct:
        // (1) (~eq1 /\ eq2 /\ phi[false/eq1, true/eq2])
        // (2) (eq2 /\ phi[true/eq2])
        // (3) (eq2 /\ phi[false/eq1, true/eq2] (this is what we do)
        //
        // all are correct, in the sense that the corresponding disjunctions are
        // equivalent to phi --
        //
        // the disjunction for (2) results from case splitting on
        // (eq1 \/ eq2 \/ ... \/ eqn) (and using distributivity);
        //
        // the disjunction for (1) results from case splitting on each eqi recursively;
        //
        // it is easy to see that (1)=>(3)=>(2) for any particular disjunct and
        // hence, the disjunction for (3) is also equivalent to phi, by transitivity,
        // and by using the fact that [(a1=>b1) /\ (a2=>b2) => ((a1\/a2) => (b1\/b2))]
        sub.insert (a, m.mk_false (), pr);
        TRACE ("qe_array",
                tout << "Sub Pair: " << mk_pp (a, m) << " " << mk_pp (m.mk_false (), m) << "\n";
              );
    }

    if (sub.empty ()) {
        result = e;
    } else {
        // erase the substitution for the variable being eliminated
        SASSERT (v);
        sub.erase (v);
        TRACE ("qe_array",
                tout << "Erasing sub for: " << mk_pp (v, m) << "\n";
              );
        // the case where all partial eqs are false;
        // to be precise, we should also be adding conjuncts explicitly stating
        //   that the partial eqs are false
        //   (conjunct for (a ==I b) would be (x \not\in I /\ a[x] != b[x]))
        // fortunately, these are redundant as such an x can always be chosen
        //   given that a only appears in select terms in the rest of the fml
        //   -- simply choose an x different from all other indices and I,
        //   and assign a[x] to something different from b[x]
        expr_ref disj (e, m);
        TRACE ("qe_array",
                tout << "Before sub:\n" << mk_pp (disj, m) << "\n";
              );
        rep->set_substitution (&sub);
        (*rep)(disj);
        TRACE ("qe_array",
                tout << "After sub:\n" << mk_pp (disj, m) << "\n";
              );
        expr_ref_vector partial_eqs (m);
        elim_stores (disj.get (), disj, partial_eqs);
        // there should be no newly generated partial eqs
        SASSERT (partial_eqs.empty ());
        TRACE ("qe_array",
                tout << "After eliminating stores:\n" << mk_pp (disj, m) << "\n";
              );
        result_disjs.push_back (disj);
        result = m.mk_or (result_disjs.size (), result_disjs.c_ptr ());
    }
}

void qe_array::generate_congruences (expr_ref_vector const& sel_exps,
                                     expr_ref_vector const& sel_consts,
                                     expr_ref_vector& result) {
    SASSERT (sel_exps.size () == sel_consts.size ());
    for (unsigned i = 0; i < sel_exps.size (); i++) {
        expr* sel_1 = sel_exps.get (i);
        expr* val_1 = sel_consts.get (i);
        SASSERT (m_arr_u.is_select (sel_1));
        expr* idx_1 = to_app (sel_1)->get_arg (1);
        for (unsigned j = i+1; j < sel_exps.size (); j++) {
            expr* sel_2 = sel_exps.get (j);
            expr* val_2 = sel_consts.get (j);
            SASSERT (m_arr_u.is_select (sel_2));
            SASSERT (m_eq_proc (to_app (sel_1)->get_arg (0),
                                to_app (sel_2)->get_arg (0)));
            expr* idx_2 = to_app (sel_2)->get_arg (1);
            // skip the congruence if both idx_1 and idx_2 are numerals,
            // as they are going to be different and the congruence is
            // vacuously true
            if (m_ari_u.is_numeral (idx_1) && m_ari_u.is_numeral (idx_2)) continue;
            app_ref idx_eq (m.mk_eq (idx_1, idx_2), m);
            app_ref val_eq (m.mk_eq (val_1, val_2), m);
            result.push_back (m.mk_implies (idx_eq, val_eq));
        }
    }
}





// qe_array_tactic (adapted from qe_tactic and qe_lite_tactic)

class qe_array_tactic : public tactic {
    
    struct imp {
        ast_manager&             m;
        qe_array                 m_qe;
        volatile bool            m_cancel;

        imp(ast_manager& m, params_ref const& p): 
            m(m),
            m_qe(m),
            m_cancel(false)
        {}

        void set_cancel(bool f) {
            m_cancel = f;
            m_qe.set_cancel(f);
        }

        void checkpoint() {
            if (m_cancel)
                throw tactic_exception(TACTIC_CANCELED_MSG);
            cooperate("qe-array");
        }
        
        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            tactic_report report("qe-array", *g);
            proof_ref new_pr(m);
            expr_ref new_f(m);
            bool produce_proofs = g->proofs_enabled();

            unsigned sz = g->size();
            for (unsigned i = 0; i < sz; i++) {
                checkpoint();
                if (g->inconsistent())
                    break;
                expr * f = g->form(i);
                if (!has_quantifiers(f))
                    continue;
                m_qe(f, new_f);
                new_pr = 0;
                if (produce_proofs) {
                    new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
                }
                g->update(i, new_f, new_pr, g->dep(i));                
            }
            g->inc_depth();
            result.push_back(g.get());
            TRACE("qe-array", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };
    
    params_ref m_params;
    imp *      m_imp;

public:
    qe_array_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }
        
    virtual ~qe_array_tactic() {
        dealloc(m_imp);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(qe_array_tactic, m, m_params);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        // m_imp->updt_params(p);
    }

   
    virtual void collect_param_descrs(param_descrs & r) {
        // m_imp->collect_param_descrs(r);
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
    }

    
    virtual void collect_statistics(statistics & st) const {
        // m_imp->collect_statistics(st);
    }

    virtual void reset_statistics() {
        // m_imp->reset_statistics();
    }

    
    virtual void cleanup() {
        ast_manager & m = m_imp->m;
        imp * d = m_imp;
        #pragma omp critical (tactic_cancel)
        {
            m_imp = 0;
        }
        dealloc(d);
        d = alloc(imp, m, m_params);
        #pragma omp critical (tactic_cancel)
        {
            m_imp = d;
        }
    }
};

tactic * mk_qe_array_tactic(ast_manager & m, params_ref const & p) {
    return alloc(qe_array_tactic, m, p);
}
