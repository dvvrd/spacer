/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_evaluator.h

Abstract:

    Evaluate expressions in a given model.

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#ifndef _MODEL_EVALUATOR_H_
#define _MODEL_EVALUATOR_H_

#include"ast.h"
#include"rewriter_types.h"
#include"params.h"
#include "array_decl_plugin.h"

class model;

typedef rewriter_exception model_evaluator_exception;

class model_evaluator {
    struct imp;
    imp *  m_imp;
public:
    model_evaluator(model & m, params_ref const & p = params_ref());
    ~model_evaluator();

    ast_manager & m () const;
    void set_model_completion(bool f);

    void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);

    void operator()(expr * t, expr_ref & r);

    void set_cancel(bool f);
    void cancel() { set_cancel(true); }
    void reset_cancel() { set_cancel(false); }
    void cleanup(params_ref const & p = params_ref());
    void reset(params_ref const & p = params_ref());
    
    unsigned get_num_steps() const;
};

/**
 * based on model_evaluator in muz/pdr/pdr_util.h
 */
class model_evaluator_array_util {
    ast_manager&    m;
    array_util      m_array;

    void eval_exprs(model& mdl, expr_ref_vector& es);

    bool extract_array_func_interp(model& mdl, expr* a, vector<expr_ref_vector>& stores, expr_ref& else_case);

public:

    model_evaluator_array_util (ast_manager& m):
        m (m),
        m_array (m)
    {}

    /**
     * best effort evaluator of extensional array equality.
     */
    void eval_array_eq(model& mdl, app* e, expr* arg1, expr* arg2, expr_ref& res);

    void eval(model& mdl, expr* e, expr_ref& r, bool model_completion = true);
};

#endif
