/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_util.h

Abstract:

    Utility functions for SPACER.

Author:

    Krystof Hoder (t-khoder) 2011-8-19.

Revision History:

--*/

#ifndef _SPACER_UTIL_H_
#define _SPACER_UTIL_H_

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

class model;
class model_core;

namespace spacer {

  inline unsigned infty_level () {return UINT_MAX;}
  
    inline bool is_infty_level(unsigned lvl) 
    { return lvl == infty_level (); }

    inline unsigned next_level(unsigned lvl) 
    { return is_infty_level(lvl)?lvl:(lvl+1); }
  
  inline unsigned prev_level (unsigned lvl)
  {
    if (is_infty_level (lvl)) return infty_level ();
    if (lvl == 0) return 0;
    return lvl -1;
  }
  
  
    struct pp_level {
        unsigned m_level;
        pp_level(unsigned l): m_level(l) {}        
    };

    inline std::ostream& operator<<(std::ostream& out, pp_level const& p) {
        if (is_infty_level(p.m_level)) {
            return out << "oo";
        }
        else {
            return out << p.m_level;
        }
    }


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
  
  
    
  class model_evaluator {
    ast_manager&           m;
    arith_util             m_arith;
    array_util             m_array;
    obj_map<expr,rational> m_numbers;
    expr_ref_vector        m_refs;
    obj_map<expr, expr*>   m_values;
    model_ref              m_model;
        
    //00 -- non-visited
    //01 -- X
    //10 -- false
    //11 -- true
    expr_mark      m1;
    expr_mark      m2;
    
    /// used by collect() 
    expr_mark      m_visited;
        

    
    void reset();
    
    /// caches the values of all constants in the given model
    void setup_model(const model_ref& model);
    /// caches the value of an expression
    void assign_value(expr* e, expr* v);
    
    /// extracts an implicant of the conjunction of formulas
    void collect(ptr_vector<expr> const& formulas, ptr_vector<expr>& tocollect);
      
    /// one-round of extracting an implicant of e. The implicant
    /// literals are stored in tocollect. The worklist is stored in todo
    void process_formula(app* e, ptr_vector<expr>& todo, ptr_vector<expr>& tocollect);
    void eval_arith(app* e);
    void eval_basic(app* e);
    void eval_eq(app* e, expr* arg1, expr* arg2);
    void eval_array_eq(app* e, expr* arg1, expr* arg2);
    void inherit_value(expr* e, expr* v);
        
    bool is_unknown(expr* x)  { return !m1.is_marked(x) && !m2.is_marked(x); }
    void set_unknown(expr* x)  { m1.mark(x, false); m2.mark(x, false); }
    bool is_x(expr* x)  { return !m1.is_marked(x) && m2.is_marked(x); }
    bool is_false(expr* x)  { return m1.is_marked(x) && !m2.is_marked(x); }
    bool is_true(expr* x)  { return m1.is_marked(x) && m2.is_marked(x); }
    void set_x(expr* x) { SASSERT(is_unknown(x)); m2.mark(x); }
    void set_v(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); }
    void set_false(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); }
    void set_true(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); m2.mark(x); }
    void set_bool(expr* x, bool v) { if (v) { set_true(x); } else { set_false(x); } }
    rational const& get_number(expr* x) const { return m_numbers.find(x); }
    void set_number(expr* x, rational const& v) 
    { 
      set_v(x); 
      m_numbers.insert(x,v); 
      TRACE("spacer_verbose", tout << mk_pp(x,m) << " " << v << "\n";); 
    }
    expr* get_value(expr* x) { return m_values.find(x); }
    void set_value(expr* x, expr* v) 
    { set_v(x); m_refs.push_back(v); m_values.insert(x, v); }
        
      
    /// evaluates all sub-formulas and terms of the input in the current model.
    /// Caches the result
    void eval_fmls(ptr_vector<expr> const & formulas);

    /// calls eval_fmls(). Then checks whether all formulas are
    /// TRUE. Returns false if at lest one formula is unknown (X)
    bool check_model(ptr_vector<expr> const & formulas);

    bool extract_array_func_interp(expr* a, vector<expr_ref_vector>& stores, 
                                   expr_ref& else_case);

    void eval_exprs(expr_ref_vector& es);
        
  public:
    model_evaluator(ast_manager& m) : m(m), m_arith(m), m_array(m), m_refs(m) {}
            
            
    /**
       \brief extract literals from formulas that satisfy formulas.

       \pre model satisfies formulas
    */
    void minimize_literals(ptr_vector<expr> const & formulas, const model_ref& mdl, 
                           expr_ref_vector& result);

    expr_ref eval_heavy (const model_ref& mdl, expr* fml);

    expr_ref eval(const model_ref& mdl, expr* e);
    expr_ref eval(const model_ref& mdl, func_decl* d);
  };

    /**
       \brief replace variables that are used in many disequalities by
       an equality using the model. 
       
       Assumption: the model satisfies the conjunctions.       
     */
    void reduce_disequalities(model& model, unsigned threshold, expr_ref& fml);

    /**
       \brief hoist non-boolean if expressions.
     */
    void hoist_non_bool_if(expr_ref& fml);

    bool is_difference_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls);

    bool is_utvpi_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls);

    /**
     * do the following in sequence
     * 1. use qe_lite to cheaply eliminate vars
     * 2. for remaining boolean vars, substitute using M
     * 3. for remaining arith vars, use LW projection
     */
    void qe_project (ast_manager& m, app_ref_vector& vars, expr_ref& fml, 
                     const model_ref& M, bool project_all_arr_stores = false);

    void qe_project (ast_manager& m, app_ref_vector& vars, expr_ref& fml, model_ref& M, expr_map& map);

  void expand_literals(ast_manager &m, expr_ref_vector& conjs);
  void compute_implicant_literals (model_evaluator &mev, const model_ref &model, 
                                   expr_ref_vector &formula, expr_ref_vector &res);
}

#endif
