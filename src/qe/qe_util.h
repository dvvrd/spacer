/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    qe_util.h

Abstract:

    Utilities for quantifiers.

Author:

    Nikolaj Bjorner (nbjorner) 2013-08-28

Revision History:

--*/
#ifndef _QE_UTIL_H_
#define _QE_UTIL_H_

#include "ast.h"
#include "uint_set.h"

namespace qe {
    /**
       \brief Collect top-level conjunctions and disjunctions.
    */
    void flatten_and(expr_ref_vector& result);

    void flatten_and(expr* fml, expr_ref_vector& result);

    void flatten_or(expr_ref_vector& result);

    void flatten_or(expr* fml, expr_ref_vector& result);

    expr_ref mk_and(expr_ref_vector const& fmls);

    expr_ref mk_or(expr_ref_vector const& fmls);

}

class is_variable_proc {
public:
    virtual bool operator()(expr* e) const = 0;
};

class is_variable_test : public is_variable_proc {
    enum is_var_kind { BY_VAR_SET, BY_VAR_SET_COMPLEMENT, BY_NUM_DECLS };
    uint_set m_var_set;
    unsigned m_num_decls;
    is_var_kind m_var_kind;
public:
    is_variable_test(uint_set const& vars, bool index_of_bound) :
        m_var_set(vars), 
        m_num_decls(0), 
        m_var_kind(index_of_bound?BY_VAR_SET:BY_VAR_SET_COMPLEMENT) {}

    is_variable_test(unsigned num_decls) :
        m_num_decls(num_decls),
        m_var_kind(BY_NUM_DECLS) {}

    virtual bool operator()(expr* e) const {
        if (!is_var(e)) {
            return false;
        }
        unsigned idx = to_var(e)->get_idx();
        switch(m_var_kind) {
        case BY_VAR_SET:
            return m_var_set.contains(idx);
        case BY_VAR_SET_COMPLEMENT:
            return !m_var_set.contains(idx);
        case BY_NUM_DECLS:
            return idx < m_num_decls;
        }
        UNREACHABLE();
        return false;
    }
};

#endif
