/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_evaluator.cpp

Abstract:

    Evaluate expressions in a given model.

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#include"model.h"
#include"model_evaluator_params.hpp"
#include"rewriter_types.h"
#include"model_evaluator.h"
#include"bool_rewriter.h"
#include"arith_rewriter.h"
#include"bv_rewriter.h"
#include"datatype_rewriter.h"
#include"array_rewriter.h"
#include"float_rewriter.h"
#include"rewriter_def.h"
#include"cooperate.h"
#include"ast_pp.h"
#include"func_interp.h"

struct evaluator_cfg : public default_rewriter_cfg {
    model &                         m_model;
    bool_rewriter                   m_b_rw;
    arith_rewriter                  m_a_rw;
    bv_rewriter                     m_bv_rw;
    array_rewriter                  m_ar_rw;
    datatype_rewriter               m_dt_rw;
    float_rewriter                  m_f_rw;
    unsigned long long              m_max_memory;
    unsigned                        m_max_steps;
    bool                            m_model_completion;
    bool                            m_cache;

    evaluator_cfg(ast_manager & m, model & md, params_ref const & p):
        m_model(md),
        m_b_rw(m),
        // We must allow customers to set parameters for arithmetic rewriter/evaluator. 
        // In particular, the maximum degree of algebraic numbers that will be evaluated.
        m_a_rw(m, p), 
        m_bv_rw(m),
        // See comment above. We want to allow customers to set :sort-store
        m_ar_rw(m, p),
        m_dt_rw(m),
        m_f_rw(m) {
        m_b_rw.set_flat(false);
        m_a_rw.set_flat(false);
        m_bv_rw.set_flat(false);
        m_bv_rw.set_mkbv2num(true);
        updt_params(p);
    }

    void updt_params(params_ref const & _p) {
        model_evaluator_params p(_p);
        m_max_memory       = megabytes_to_bytes(p.max_memory());
        m_max_steps        = p.max_steps();
        m_model_completion = p.completion();
        m_cache            = p.cache();
    }
        
    ast_manager & m() const { return m_model.get_manager(); }

    // Try to use the entries to quickly evaluate the fi
    bool eval_fi(func_interp * fi, unsigned num, expr * const * args, expr_ref & result) {
        if (fi->num_entries() == 0)
            return false; // let get_macro handle it.

        SASSERT(fi->get_arity() == num);

        bool actuals_are_values = true;
    
        for (unsigned i = 0; actuals_are_values && i < num; i++) {
            actuals_are_values = m().is_value(args[i]);
        }
        
        if (!actuals_are_values)
            return false; // let get_macro handle it

        func_entry * entry = fi->get_entry(args);
        if (entry != 0) {
            result = entry->get_result();
            return true;
        }

        return false;
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = 0;
        family_id fid = f->get_family_id();
        if (fid == null_family_id) {
            if (num == 0) {
                expr * val = m_model.get_const_interp(f);
                if (val != 0) {
                    result = val;
                    return BR_DONE;
                }
                
                if (m_model_completion) {
                    sort * s   = f->get_range();
                    expr * val = m_model.get_some_value(s);
                    m_model.register_decl(f, val);
                    result = val;
                    return BR_DONE;
                }
                return BR_FAILED;
            }
            SASSERT(num > 0);
            func_interp * fi = m_model.get_func_interp(f);
            if (fi != 0 && eval_fi(fi, num, args, result)) {
                TRACE("model_evaluator", tout << "reduce_app " << f->get_name() << "\n";
                      for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << "\n";
                      tout << "---->\n" << mk_ismt2_pp(result, m()) << "\n";);
                return BR_DONE;
            }
        }

        if (fid == m_b_rw.get_fid()) {
            decl_kind k = f->get_decl_kind();
            if (k == OP_EQ) {
                // theory dispatch for =
                SASSERT(num == 2);
                family_id s_fid = m().get_sort(args[0])->get_family_id();
                br_status st = BR_FAILED;
                if (s_fid == m_a_rw.get_fid())
                    st = m_a_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_bv_rw.get_fid())
                    st = m_bv_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_dt_rw.get_fid())
                    st = m_dt_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_f_rw.get_fid())
                    st = m_f_rw.mk_eq_core(args[0], args[1], result);
                if (st != BR_FAILED)
                    return st;
            }
            return m_b_rw.mk_app_core(f, num, args, result);
        }
        if (fid == m_a_rw.get_fid())
            return m_a_rw.mk_app_core(f, num, args, result);
        if (fid == m_bv_rw.get_fid())
            return m_bv_rw.mk_app_core(f, num, args, result);
        if (fid == m_ar_rw.get_fid()) 
            return m_ar_rw.mk_app_core(f, num, args, result);
        if (fid == m_dt_rw.get_fid())
            return m_dt_rw.mk_app_core(f, num, args, result);
        if (fid == m_f_rw.get_fid())
            return m_f_rw.mk_app_core(f, num, args, result);
        return BR_FAILED;
    }

    bool get_macro(func_decl * f, expr * & def, quantifier * & q, proof * & def_pr) { 
        if (f->get_family_id() == null_family_id) {
            func_interp * fi = m_model.get_func_interp(f);
            
            if (fi != 0) {
                if (fi->is_partial()) {
                    if (m_model_completion) {
                        sort * s   = f->get_range();
                        expr * val = m_model.get_some_value(s);
                        fi->set_else(val);
                    }
                    else {
                        return false;
                    }
                }
                
                def    = fi->get_interp();
                SASSERT(def != 0);
                return true;
            }
            
            if (m_model_completion) {
                sort * s   = f->get_range();
                expr * val = m_model.get_some_value(s);
                func_interp * new_fi = alloc(func_interp, m(), f->get_arity());
                new_fi->set_else(val);
                m_model.register_decl(f, new_fi);
                def = val;
                return true;
            }
        }
        return false;
    }
    
    bool max_steps_exceeded(unsigned num_steps) const { 
        cooperate("model evaluator");
        if (memory::get_allocation_size() > m_max_memory)
            throw rewriter_exception(Z3_MAX_MEMORY_MSG);
        return num_steps > m_max_steps;
    }

    bool cache_results() const { return m_cache; }

};

template class rewriter_tpl<evaluator_cfg>;

struct model_evaluator::imp : public rewriter_tpl<evaluator_cfg> {
    evaluator_cfg m_cfg;
    imp(model & md, params_ref const & p):
        rewriter_tpl<evaluator_cfg>(md.get_manager(), 
                                    false, // no proofs for evaluator
                                    m_cfg),
        m_cfg(md.get_manager(), md, p) {
    }
};

model_evaluator::model_evaluator(model & md, params_ref const & p) {
    m_imp = alloc(imp, md, p);
}

ast_manager & model_evaluator::m() const {
    return m_imp->m();
}

model_evaluator::~model_evaluator() {
    dealloc(m_imp);
}

void model_evaluator::updt_params(params_ref const & p) {
    m_imp->cfg().updt_params(p);
}

void model_evaluator::get_param_descrs(param_descrs & r) {
    model_evaluator_params::collect_param_descrs(r);
}

void model_evaluator::set_model_completion(bool f) {
    m_imp->cfg().m_model_completion = f;
}

unsigned model_evaluator::get_num_steps() const {
    return m_imp->get_num_steps();
}

void model_evaluator::set_cancel(bool f) {
    #pragma omp critical (model_evaluator)
    {
        m_imp->set_cancel(f);
    }
}

void model_evaluator::cleanup(params_ref const & p) {
    model & md = m_imp->cfg().m_model;
    #pragma omp critical (model_evaluator)
    {
        dealloc(m_imp);
        m_imp = alloc(imp, md, p);
    }
}

void model_evaluator::reset(params_ref const & p) {
    m_imp->reset();
    updt_params(p);
}

void model_evaluator::operator()(expr * t, expr_ref & result) {
    TRACE("model_evaluator", tout << mk_ismt2_pp(t, m()) << "\n";);
    m_imp->operator()(t, result);
}


// model_evaluator_array_util


void model_evaluator_array_util::eval_exprs(model& mdl, expr_ref_vector& es) {
    for (unsigned j = 0; j < es.size(); ++j) {
        if (m_array.is_as_array(es.get (j))) {
            expr_ref r (m);
            eval(mdl, es.get (j), r);
            es.set (j, r);
        }
    }
}

bool model_evaluator_array_util::extract_array_func_interp(model& mdl, expr* a, vector<expr_ref_vector>& stores, expr_ref& else_case) {
    SASSERT(m_array.is_array(a));

    TRACE("model_evaluator", tout << mk_pp(a, m) << "\n";);
    while (m_array.is_store(a)) {
        expr_ref_vector store(m);
        store.append(to_app(a)->get_num_args()-1, to_app(a)->get_args()+1);
        eval_exprs(mdl, store);
        stores.push_back(store);
        a = to_app(a)->get_arg(0);
    }

    if (m_array.is_const(a)) {
        else_case = to_app(a)->get_arg(0);
        return true;
    }

    while (m_array.is_as_array(a)) {
        func_decl* f = m_array.get_as_array_func_decl(to_app(a));
        func_interp* g = mdl.get_func_interp(f);
        unsigned sz = g->num_entries();
        unsigned arity = f->get_arity();
        for (unsigned i = 0; i < sz; ++i) {
            expr_ref_vector store(m);
            func_entry const* fe = g->get_entry(i);
            store.append(arity, fe->get_args());
            store.push_back(fe->get_result());
            for (unsigned j = 0; j < store.size(); ++j) {
                if (!is_ground(store[j].get())) {
                    TRACE("model_evaluator", tout << "could not extract array interpretation: " << mk_pp(a, m) << "\n" << mk_pp(store[j].get(), m) << "\n";);
                    return false;
                }
            }
            eval_exprs(mdl, store);
            stores.push_back(store);
        }        
        else_case = g->get_else();
        if (!else_case) {
            TRACE("model_evaluator", tout << "no else case " << mk_pp(a, m) << "\n";);
            return false;
        }
        if (!is_ground(else_case)) {
            TRACE("model_evaluator", tout << "non-ground else case " << mk_pp(a, m) << "\n" << mk_pp(else_case, m) << "\n";);
            return false;
        }
        if (m_array.is_as_array(else_case)) {
            expr_ref r (m);
            eval(mdl, else_case, r);
            else_case = r;
        }
        TRACE("model_evaluator", tout << "else case: " << mk_pp(else_case, m) << "\n";);
        return true;
    }
    TRACE("model_evaluator", tout << "no translation: " << mk_pp(a, m) << "\n";);

    return false;
}

void model_evaluator_array_util::eval_array_eq(model& mdl, app* e, expr* arg1, expr* arg2, expr_ref& res) {
    TRACE("model_evaluator", tout << "array equality: " << mk_pp(e, m) << "\n";);
    expr_ref v1(m), v2(m);
    eval (mdl, arg1, v1);
    eval (mdl, arg2, v2);
    if (v1 == v2) {
        res = m.mk_true ();
        return;
    }
    sort* s = m.get_sort(arg1);
    sort* r = get_array_range(s);
    // give up evaluating finite domain/range arrays
    if (!r->is_infinite() && !r->is_very_big() && !s->is_infinite() && !s->is_very_big()) {
        TRACE("model_evaluator", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
        res.reset ();
        return;
    }
    vector<expr_ref_vector> store;
    expr_ref else1(m), else2(m);
    if (!extract_array_func_interp(mdl, v1, store, else1) ||
            !extract_array_func_interp(mdl, v2, store, else2)) {
        TRACE("model_evaluator", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
        res.reset ();
        return;
    }

    if (else1 != else2) {
        if (m.is_value(else1) && m.is_value(else2)) {
            TRACE("model_evaluator", tout 
                    << "defaults are different: " << mk_pp(e, m) << " " 
                    << mk_pp(else1, m) << " " << mk_pp(else2, m) << "\n";);
            res = m.mk_false ();
        }
        else if (m_array.is_array(else1)) {
            eval_array_eq(mdl, e, else1, else2, res);
        }
        else {
            TRACE("model_evaluator", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
            res.reset ();
        }
        return;
    }

    expr_ref s1(m), s2(m), w1(m), w2(m);        
    expr_ref_vector args1(m), args2(m);
    args1.push_back(v1);
    args2.push_back(v2);        
    for (unsigned i = 0; i < store.size(); ++i) {
        args1.resize(1);
        args2.resize(1);
        args1.append(store[i].size()-1, store[i].c_ptr());
        args2.append(store[i].size()-1, store[i].c_ptr());
        s1 = m_array.mk_select(args1.size(), args1.c_ptr());
        s2 = m_array.mk_select(args2.size(), args2.c_ptr());
        eval (mdl, s1, w1);
        eval (mdl, s2, w2);
        if (w1 == w2) {
            continue;
        }
        if (m.is_value(w1) && m.is_value(w2)) {
            TRACE("model_evaluator", tout << "Equality evaluation: " << mk_pp(e, m) << "\n"; 
                    tout << mk_pp(s1, m) << " |-> " << mk_pp(w1, m) << "\n";
                    tout << mk_pp(s2, m) << " |-> " << mk_pp(w2, m) << "\n";);
            res = m.mk_false ();
        }
        else if (m_array.is_array(w1)) {
            eval_array_eq(mdl, e, w1, w2, res);
            if (m.is_true (res)) {
                continue;
            }
        }
        else {
            TRACE("model_evaluator", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
            res.reset ();
        }
        return;
    }
    res = m.mk_true ();
}

void model_evaluator_array_util::eval(model& mdl, expr* e, expr_ref& r, bool model_completion) {
    model_evaluator mev (mdl);
    mev.set_model_completion (model_completion);
    bool eval_result = true;
    try {
        mev (e, r);
    }
    catch (model_evaluator_exception &) {
        eval_result = false;
    }
    VERIFY(eval_result);

    if (m_array.is_array(e)) {
        vector<expr_ref_vector> stores;
        expr_ref_vector args(m);
        expr_ref else_case(m);
        if (extract_array_func_interp(mdl, r, stores, else_case)) {
            r = m_array.mk_const_array(m.get_sort(e), else_case);
            while (!stores.empty() && stores.back().back() == else_case) {
                stores.pop_back();
            }
            for (unsigned i = stores.size(); i > 0; ) {
                --i;
                args.resize(1);
                args[0] = r;
                args.append(stores[i]);
                r = m_array.mk_store(args.size(), args.c_ptr());
            }
            return;
        }
    }
    return;
}
