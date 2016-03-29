#include "spacer_virtual_solver.h"
#include "ast_util.h"
#include "spacer_util.h"
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
    SASSERT (!m_pushed || get_scope_level () > 0);
    if (m_pushed) pop (get_scope_level ());
    
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
    SASSERT (!m_pushed || get_scope_level () > 0);
    scoped_watch _t_(m_factory.m_check_watch);
    m_factory.m_stats.m_num_smt_checks++;
    
    stopwatch sw;
    sw.start ();
    internalize_assertions ();
    lbool res = m_context.check (num_assumptions, assumptions);
    if (res == l_true)
    {
      sw.stop ();
      m_factory.m_check_sat_watch.add (sw);
      m_factory.m_stats.m_num_sat_smt_checks++;
    }
    
    set_status (res);
    return res;
  }
  
  void virtual_solver::push_core ()
  {
    SASSERT (!m_pushed || get_scope_level () > 0);
    if (m_in_delay_scope)
    {
      // second push
      internalize_assertions ();
      m_context.push ();
      m_pushed = true;
      m_in_delay_scope = false;
    }
    
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
    SASSERT (!m_pushed || get_scope_level () > 0);
    if (m_pushed)
    {
      SASSERT (!m_in_delay_scope);
      m_context.pop (n);
      m_pushed = get_scope_level () - n > 0;
    }
    else
      m_in_delay_scope = get_scope_level () - n > 0;
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
    SASSERT (!m_pushed || get_scope_level () > 0);
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

  virtual_solver_factory::virtual_solver_factory (ast_manager &mgr, smt_params &fparams) :
    m_params (fparams), m(mgr), m_context (m, m_params), m_num_solvers(0)
  {
    // m_params.updt_params (p);
    m_stats.reset ();
  }
  
  virtual_solver* virtual_solver_factory::mk_solver ()
  {
    std::stringstream name;
    name << "#solver" << m_num_solvers++;
    app_ref pred(m);
    pred = m.mk_const (symbol (name.str ().c_str ()), m.mk_bool_sort ());
    SASSERT (m_context.get_scope_level () == 0);
    return alloc (virtual_solver, *this, m_context, pred);
  }

  void virtual_solver_factory::collect_statistics (statistics &st) const
  {
    m_context.collect_statistics (st);
    st.update ("time.virtual_solver.smt.total", m_check_watch.get_seconds ());
    st.update ("time.virtual_solver.smt.total.sat", m_check_sat_watch.get_seconds ());
    st.update ("virtual_solver.checks", m_stats.m_num_smt_checks);
    st.update ("virtual_solver.checks.sat", m_stats.m_num_sat_smt_checks);
  }
  void virtual_solver_factory::reset_statistics ()
  {
    m_context.reset_statistics ();
    m_stats.reset ();
    m_check_sat_watch.reset ();
    m_check_watch.reset ();
  }
  
  


  
}
