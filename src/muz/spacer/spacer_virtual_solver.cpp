#include "spacer_virtual_solver.h"
#include "ast_util.h"

namespace spacer
{
  virtual_solver::virtual_solver (virtual_solver_factory &factory,
                                  smt::kernel &context, app* pred) :
    solver_na2as (context.m()),
    m_factory (factory),
    m(context.m()),
    m_context (context),
    m_pred (pred, m),
    m_virtual (!m.is_true (pred)),
    m_assertions (m),
    m_head (0),
    m_flat (m),
    m_pushed (false),
    m_in_delay_scope (false)
  {
    // -- insert m_pred->true background assumption this will not
    // -- change m_context, but will add m_pred to
    // -- the private field solver_na2as::m_assumptions
    if (m_virtual)
      solver_na2as::assert_expr (m.mk_true (), m_pred);
  }

  virtual_solver::~virtual_solver ()
  {
    if (m_pushed) pop (this->get_scope_level ());
    if (m_virtual) 
    {
      m_pred = m.mk_not (m_pred);
      m_context.assert_expr (m_pred);
    }
  }
  
  bool virtual_solver::is_aux_predicate (expr *p)
  {return is_app (p) && to_app (p) == m_pred.get ();}
  
  lbool virtual_solver::check_sat_core (unsigned num_assumptions,
                                        expr *const * assumptions)
  {
    internalize_assertions ();
    lbool res = m_context.check (num_assumptions, assumptions);
    set_status (res);
    return res;
  }
  
  void virtual_solver::push_core ()
  {
    if (!m_pushed) m_in_delay_scope = true;
    else 
    {
      SASSERT (m_pushed);
      SASSERT (!m_in_delay_scope);
      m_context.push ();
    }
  }
  void virtual_solver::pop_core (unsigned n)
  {
    if (m_pushed) m_context.pop (n);
    m_pushed = m_context.get_scope_level () > 0;
    m_in_delay_scope = !m_pushed && get_scope_level () - n > 0;
  }
  
  void virtual_solver::get_unsat_core (ptr_vector<expr> &r)
  {
    for (unsigned i = 0, sz = m_context.get_unsat_core_size (); i < sz; ++i)
    {
      expr *core = m_context.get_unsat_core_expr (i);
      if (is_aux_predicate (core)) continue;
      r.push_back (core);
    }
  }
  
  void virtual_solver::assert_expr (expr *e)
  {
    if (m.is_true(e)) return;
    if (m_in_delay_scope)
    {
      internalize_assertions ();
      m_context.push ();
      m_pushed = true;
      m_in_delay_scope = false;
    }
    
    if (m_pushed)
      m_context.assert_expr (e);
    else
    {
      m_flat.push_back (e);
      flatten_and (m_flat);
      m_assertions.append (m_flat);
      m_flat.reset ();
    }    
  }
  void virtual_solver::internalize_assertions ()
  {
    SASSERT (!m_pushed || m_head == m_assertions.size ());
    for (unsigned sz = m_assertions.size (); m_head < sz; ++m_head)
    {
      expr_ref f(m);
      f = m.mk_implies (m_pred, (m_assertions.get (m_head)));
      m_context.assert_expr (f);
    }
  }
  void virtual_solver::get_labels(svector<symbol> &r)
  {
    r.reset();
    buffer<symbol> tmp;
    m_context.get_relevant_labels(0, tmp);
    r.append(tmp.size(), tmp.c_ptr());
  }
  
  solver* virtual_solver::translate(ast_manager& m, params_ref const& p) {
    UNREACHABLE();
    return 0;
  }

  virtual_solver_factory::virtual_solver_factory (ast_manager &mgr, params_ref const &p) :
    m_params (p), m(mgr), m_context (m, m_params), m_num_solvers(0)
  {m_params.updt_params (p);}
  
  virtual_solver* virtual_solver_factory::mk_solver ()
  {
    std::stringstream name;
    name << "#solver" << m_num_solvers++;
    app_ref pred(m);
    pred = m.mk_const (symbol (name.str ().c_str ()), m.mk_bool_sort ());
    return alloc (virtual_solver, *this, m_context, pred);
  }
  


  
}
