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
        expr_mark      m_visited;
        

        void reset();
        void setup_model(model_ref& model);
        void assign_value(expr* e, expr* v);
        void collect(ptr_vector<expr> const& formulas, ptr_vector<expr>& tocollect);
        void process_formula(app* e, ptr_vector<expr>& todo, ptr_vector<expr>& tocollect);
        expr_ref_vector prune_by_cone_of_influence(ptr_vector<expr> const & formulas);
        void eval_arith(app* e);
        void eval_basic(app* e);
        void eval_eq(app* e, expr* arg1, expr* arg2);
        void eval_array_eq(app* e, expr* arg1, expr* arg2);
        void inherit_value(expr* e, expr* v);
        
        inline bool is_unknown(expr* x)  { return !m1.is_marked(x) && !m2.is_marked(x); }
        inline void set_unknown(expr* x)  { m1.mark(x, false); m2.mark(x, false); }
        inline bool is_x(expr* x)  { return !m1.is_marked(x) && m2.is_marked(x); }
        inline bool is_false(expr* x)  { return m1.is_marked(x) && !m2.is_marked(x); }
        inline bool is_true(expr* x)  { return m1.is_marked(x) && m2.is_marked(x); }
        inline void set_x(expr* x) { SASSERT(is_unknown(x)); m2.mark(x); }
        inline void set_v(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); }
        inline void set_false(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); }
        inline void set_true(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); m2.mark(x); }
        inline void set_bool(expr* x, bool v) { if (v) { set_true(x); } else { set_false(x); } }
        inline rational const& get_number(expr* x) const { return m_numbers.find(x); }
        inline void set_number(expr* x, rational const& v) { 
            set_v(x); TRACE("spacer_verbose", tout << mk_pp(x,m) << " " << v << "\n";); m_numbers.insert(x,v); 
        }
        inline expr* get_value(expr* x) { return m_values.find(x); }
        inline void set_value(expr* x, expr* v) { set_v(x); m_refs.push_back(v); m_values.insert(x, v); }
        
        void eval_fmls(ptr_vector<expr> const & formulas, bool model_completion = false);

        bool check_model(ptr_vector<expr> const & formulas);

        bool extract_array_func_interp(expr* a, vector<expr_ref_vector>& stores, expr_ref& else_case);

        void eval_exprs(expr_ref_vector& es);
        
    public:
        model_evaluator(ast_manager& m) : m(m), m_arith(m), m_array(m), m_refs(m) {}
            
        /**
           \brief extract equalities from model that suffice to satisfy formula.
               
           \pre model satisfies formulas
        */
            
       expr_ref_vector minimize_model(ptr_vector<expr> const & formulas, model_ref& mdl);
            
       /**
          \brief extract literals from formulas that satisfy formulas.

          \pre model satisfies formulas
       */
       void minimize_literals(ptr_vector<expr> const & formulas, model_ref& mdl, expr_ref_vector& result);

       /** 
           for_each_expr visitor.
       */
       void operator()(expr* e) {} 

       void eval_heavy (model_ref& mdl, expr* fml, expr_ref& result, bool model_completion = true);

       expr_ref eval(model_ref& mdl, expr* e, bool model_completion = true);

       expr_ref eval(model_ref& mdl, func_decl* d);
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
     * 3. use MBP for remaining array and arith variables
     * 4. for any remaining arith variables, substitute using M
     */
    void qe_project (ast_manager& m, app_ref_vector& vars, expr_ref& fml, model_ref& M, bool reduce_all_selects = false);

    void qe_project (ast_manager& m, app_ref_vector& vars, expr_ref& fml, model_ref& M, expr_map& map);

  void expand_literals(ast_manager &m, expr_ref_vector& conjs);
}

#endif
