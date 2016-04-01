/** 
Spacer
Copyright (c) 2015 Carnegie Mellon University.
All Rights Reserved.

THIS SOFTWARE IS PROVIDED "AS IS," WITH NO WARRANTIES
WHATSOEVER. CARNEGIE MELLON UNIVERSITY EXPRESSLY DISCLAIMS TO THE
FULLEST EXTENT PERMITTEDBY LAW ALL EXPRESS, IMPLIED, AND STATUTORY
WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND
NON-INFRINGEMENT OF PROPRIETARY RIGHTS.

Released under a modified MIT license, please see SPACER_LICENSE.txt
for full terms.  DM-0002483

Spacer includes and/or makes use of the following Third-Party Software
subject to its own license:

Z3
Copyright (c) Microsoft Corporation
All rights reserved.

Released under the MIT License (LICENSE.txt)

Module Name:

    spacer_virtual_solver.h

Abstract:

   multi-solver view of a single smt::kernel

Author:

    Arie Gurfinkel

Notes:
   
--*/
#ifndef SPACER_VIRTUAL_SOLVER_H_
#define SPACER_VIRTUAL_SOLVER_H_
#include"ast.h"
#include"params.h"
#include"solver_na2as.h"
#include"smt_kernel.h"
#include"smt_params.h"
#include"stopwatch.h"
namespace spacer
{
  class virtual_solver_factory;
  
  class virtual_solver : public solver_na2as
  {
    friend class virtual_solver_factory;
    
  private:
    virtual_solver_factory &m_factory;
    ast_manager &m;
    smt::kernel &m_context;
    app_ref m_pred;

    bool m_virtual;
    expr_ref_vector m_assertions;
    unsigned m_head;
    expr_ref_vector m_flat;

    bool m_pushed;
    bool m_in_delay_scope;

    proof_ref m_proof;
    
    virtual_solver (virtual_solver_factory &factory, smt::kernel &context, app* pred);
    
    bool is_aux_predicate (expr *p);
    void internalize_assertions ();
    
  public:
    virtual ~virtual_solver ();
    virtual unsigned get_num_assumptions () const 
    {
      unsigned sz = solver_na2as::get_num_assumptions ();
      return m_virtual ? sz - 1 : sz;
    }
    virtual expr* get_assumption (unsigned idx) const
    {
      if (m_virtual) idx--;
      return solver_na2as::get_assumption (idx);
    }

    virtual void get_unsat_core (ptr_vector<expr> &r);
    virtual void assert_expr (expr *e);
    virtual void collect_statistics (statistics &st) const {}
    virtual void get_model (model_ref &m) {m_context.get_model (m);} 
    virtual proof* get_proof ();
    virtual std::string reason_unknown () const 
    {return m_context.last_failure_as_string ();}
    virtual void set_reason_unknown(char const *msg)
    {m_context.set_reason_unknown (msg);} 
    virtual ast_manager& get_manager () {return m;}
    virtual void get_labels(svector<symbol> &r);
    
    virtual void set_progress_callback(progress_callback *callback)
    {UNREACHABLE ();}
    
    virtual solver *translate (ast_manager &m, params_ref const &p);
    
    
  protected:
    virtual lbool check_sat_core (unsigned num_assumptions, expr *const * assumptions);
    virtual void push_core();
    virtual void pop_core (unsigned n);
  };

  /// multi-solver abstraction on top of a single smt::kernel
  class virtual_solver_factory
  {
    friend class virtual_solver;
  private:
    smt_params  &m_params;
    ast_manager &m;
    smt::kernel m_context;
    /// number of solvers created by this factory so-far
    unsigned m_num_solvers;
    
    struct stats {
      unsigned m_num_smt_checks;
      unsigned m_num_sat_smt_checks;
      stats() { reset(); }
      void reset() { memset(this, 0, sizeof(*this)); }
    };
    
    stats m_stats;
    stopwatch m_check_watch;
    stopwatch m_check_sat_watch;
    stopwatch m_proof_watch;

    
  public:
    virtual_solver_factory (ast_manager &mgr, smt_params &fparams);
    virtual_solver* mk_solver ();
    void collect_statistics (statistics &st) const;
    void reset_statistics ();
    void reset () 
    {
      m_context.reset ();
      m_num_solvers = 0;
    }
  };
    
}


#endif
