/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    prop_solver.h

Abstract:

    SAT solver abstraction for SPACER.

Author:

    Krystof Hoder (t-khoder) 2011-8-17.

Revision History:

--*/

#ifndef _PROP_SOLVER_H_
#define _PROP_SOLVER_H_

#include <map>
#include <string>
#include <utility>
#include "ast.h"
#include "obj_hashtable.h"
#include "smt_kernel.h"
#include "util.h"
#include "vector.h"
#include "spacer_manager.h"
#include "spacer_smt_context_manager.h"

struct fixedpoint_params;

namespace spacer {
    class prop_solver {
    
    private:
        smt_params&         m_fparams;        
        ast_manager&        m;
        manager&            m_pm;
        symbol              m_name;
        bool                m_try_minimize_core;
        scoped_ptr<spacer::smt_context> m_ctx;
        decl_vector         m_level_preds;      
        app_ref_vector      m_pos_level_atoms;  // atoms used to identify level
        app_ref_vector      m_neg_level_atoms;  // 
        obj_hashtable<expr> m_level_atoms_set;
        obj_hashtable<expr> m_aux_pred_set;
        app_ref_vector      m_proxies;          // predicates for assumptions
        expr_ref_vector*    m_core; 
        model_ref*          m_model;
        bool                m_subset_based_core;
        unsigned            m_uses_level;
        /// if true sets the solver into a delta level, enabling only
        /// atoms explicitly asserted in m_current_level
        bool                m_delta_level;
        bool                m_in_level;         
        unsigned            m_current_level;    // set when m_in_level
        bool                m_validate_theory_core;// flag for validating theory cores
        
        /** Add level atoms activating certain level into a vector */
        void push_level_atoms(unsigned level, expr_ref_vector & tgt) const;
        
        void ensure_level(unsigned lvl);

        class safe_assumptions;

        // validate if theory core is actually inconsistent with the context
        // for integers, farkas core need not be sound
        bool validate_theory_core ();

        void extract_theory_core(safe_assumptions& assumptions);

        void extract_subset_core(safe_assumptions& assumptions, expr* const* unsat_core = 0, unsigned unsat_core_size = 0);
        
        lbool check_safe_assumptions(
            safe_assumptions& assumptions,
            expr_ref_vector const& hard_atoms,
            expr_ref_vector& soft_atoms);
        
        
    public:
        prop_solver(spacer::manager& pm, fixedpoint_params const& p, symbol const& name, bool validate_theory_core);
        
        

      void add_aux_predicate (expr *p)
      {if (!is_aux_predicate (p)) m_aux_pred_set.insert (p);}
      
      void reset_aux_predicates () {m_aux_pred_set.reset ();}
      
      bool is_aux_predicate (expr *p)
      {return m_ctx->is_aux_predicate (p) || m_aux_pred_set.contains (p);}
      

        void set_core(expr_ref_vector* core) { m_core = core; }
        void set_model(model_ref* mdl) { m_model = mdl; }
        void set_subset_based_core(bool f) { m_subset_based_core = f; }
        bool assumes_level() const { return !is_infty_level (m_uses_level); }
        unsigned uses_level () const {return m_uses_level;}
      
        
        void add_level();
        unsigned level_cnt() const;
        
        class scoped_level {
            bool& m_lev;
        public:
            scoped_level(prop_solver& ps, unsigned lvl):m_lev(ps.m_in_level) { 
                SASSERT(!m_lev); m_lev = true; ps.m_current_level = lvl; 
            }
            ~scoped_level() { m_lev = false; }
        };
      
      class scoped_delta_level : public scoped_level
      {
        bool &m_delta;
      public:
        scoped_delta_level (prop_solver &ps, unsigned lvl) : 
          scoped_level (ps, lvl), m_delta (ps.m_delta_level) {m_delta = true;}
        ~scoped_delta_level() {m_delta = false;}
      };
        
        
      class scoped_subset_core
      {
        prop_solver &m_ps;
        bool m_subset_based_core;
        
      public: 
        scoped_subset_core (prop_solver &ps, bool subset_core) : 
          m_ps(ps), m_subset_based_core (ps.m_subset_based_core)
        {m_ps.set_subset_based_core (subset_core);}
        
        ~scoped_subset_core () 
        {m_ps.set_subset_based_core (m_subset_based_core);}
      };
      
        void add_formula(expr * form);
        void add_level_formula(expr * form, unsigned level);
                
        /**
         * check assumptions with a background formula
         */
        lbool check_assumptions (const expr_ref_vector & hard_atoms, 
                                 expr_ref_vector & soft_atoms, 
                                 unsigned num_bg = 0,
                                 expr * const *bg = NULL);
        
        void collect_statistics(statistics& st) const;

        void reset_statistics();
        
    };
}


#endif
