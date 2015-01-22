/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_util.h

Abstract:

    Utility functions for PDR.

Author:

    Krystof Hoder (t-khoder) 2011-8-19.

Revision History:

--*/

#ifndef _PDR_UTIL_H_
#define _PDR_UTIL_H_

#include "ast.h"
#include "ast_pp.h"
#include "obj_hashtable.h"
#include "ref_vector.h"
#include "simplifier.h"
#include "trace.h"
#include "vector.h"
#include "arith_decl_plugin.h"
#include "array_decl_plugin.h"
#include "bv_decl_plugin.h"

#include "model_evaluator.h"
#include "model_evaluator_array.h"
#include "th_rewriter.h"

class model;
class model_core;

namespace pdr {

    /**
     * Return the ceiling of base 2 logarithm of a number, 
     * or zero if the nmber is zero.
     */
    unsigned ceil_log2(unsigned u);

    typedef ptr_vector<app> app_vector;
    typedef ptr_vector<func_decl> decl_vector;
    typedef obj_hashtable<func_decl> func_decl_set;
    
    std::string pp_cube(const ptr_vector<expr>& model, ast_manager& manager);
    std::string pp_cube(const expr_ref_vector& model, ast_manager& manager);
    std::string pp_cube(const ptr_vector<app>& model, ast_manager& manager);
    std::string pp_cube(const app_ref_vector& model, ast_manager& manager);
    std::string pp_cube(unsigned sz, app * const * lits, ast_manager& manager);
    std::string pp_cube(unsigned sz, expr * const * lits, ast_manager& manager);
    

    /**
       \brief replace variables that are used in many disequalities by
       an equality using the model. 
       
       Assumption: the model satisfies the conjunctions.       
     */
    void reduce_disequalities(model& model, unsigned threshold, expr_ref& fml);

    /**
       \brief normalize coefficients in polynomials so that least coefficient is 1.
     */
    void normalize_arithmetic(expr_ref& t);

  /**
   * \brief replace variables in fml by fresh constants
   */
  void replace_vars_by_consts (expr* fml, expr_ref& result, expr_ref_vector& consts, ast_manager& m);

    /**
       \brief determine if formulas belong to difference logic or UTVPI fragment.
     */
    bool is_difference_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls);

  bool is_utvpi_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls);

  class select_reducer
  {
    ast_manager &m;
    array_util m_au;
    model_evaluator_array_util m_mev;
    th_rewriter m_rw;
    model_ref m_model;
    
    expr_ref_vector m_side;
    expr_ref_vector m_pinned;
    obj_map<app, expr*> m_cache;
    
    bool is_equals (expr *e1, expr *e2);
    expr *reduce_expr (expr *lit);
    expr *reduce_select (app *e);
    
  public:
    select_reducer (ast_manager &manager, model_ref &model);
    void reset ();
    void operator() (expr_ref &fml);
    
  };
  
  void expand_literals(ast_manager &m, expr_ref_vector& conjs);

}

#endif
