/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_smt_context_manager.cpp

Abstract:

    Manager of smt contexts

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-26.

Revision History:

--*/

#include "spacer_smt_context_manager.h"
#include "has_free_vars.h"
#include "ast_pp.h"
#include "ast_smt_pp.h"
#include <sstream>
#include "smt_params.h"

namespace spacer {

    smt_context::scoped::scoped(smt_context& ctx): m_ctx(ctx) {
        SASSERT(!m_ctx.m_in_delay_scope);
        SASSERT(!m_ctx.m_pushed);
        m_ctx.m_in_delay_scope = true;
    }

    smt_context::scoped::~scoped() {
        SASSERT(m_ctx.m_in_delay_scope);
        if (m_ctx.m_pushed) m_ctx.pop(); 
        m_ctx.m_in_delay_scope = false;        
    }


    smt_context::smt_context(smt::kernel & ctx, smt_context_manager& p, app* pred):
      m_pred(pred, ctx.m()),
      m_parent(p),
      m_in_delay_scope(false),
      m_pushed(false),
      m (ctx.m ()),
      m_context(ctx),
      m_virtual (!m.is_true (pred)),
      m_assertions(m),
      m_head(0)
    {}

    smt_context::~smt_context ()
    {
      ast_manager &m = m_context.m();
      /// turn off any constraints that dependent on this context
      if (m_virtual)
      {
        /// it should be safe to assert under a scope, but I would
        /// like to know if this ever happens.  Remove this assertion
        /// if it is causing issues.
        SASSERT (m_context.get_scope_level () == 0);
        m_context.assert_expr (m.mk_not (m_pred));
      }
    }
  
  void smt_context::internalize_assertions ()
  {
    SASSERT (!m_pushed);
    for (unsigned sz = m_assertions.size (); m_head < sz; ++m_head)
    {
      expr_ref f(m);
#if 1
      f = m.mk_implies (m_pred, (m_assertions.get (m_head)));
      m_context.assert_expr (f);
#else      
      expr_ref_vector v(m);
      v.push_back (m_assertions.get (m_head));
      flatten_and (v);
      for (unsigned i = 0, vsz = v.size (); i < vsz; ++i)
      {
        f = m.mk_implies (m_pred, v.get (i));
        m_context.assert_expr (f);
      }
#endif
    }
    
  }
  
  void smt_context::push()
  {
    SASSERT (!m_pushed);
    internalize_assertions ();
    m_context.push();
    m_pushed = true;
  }

  void smt_context::assert_expr (expr* e)
  {
    if (m.is_true(e)) return;
    if (m_in_delay_scope && !m_pushed) push ();
        
    if (m_pushed)
      m_context.assert_expr (e);
    else
      flatten_and (e, m_assertions);
  }

  void smt_context::assert_lemma (expr *t)
  {
    if (!m_pushed) internalize_assertions ();
    m_context.assert_expr (t);
  }

  void smt_context::reset (void)
  {
    SASSERT (!m_pushed);
    SASSERT (!m_virtual);
    m_context.reset ();
    m_head = 0;
  }
  
    
    lbool smt_context::check (expr_ref_vector& assumptions)
    {
      if (!m_pushed) internalize_assertions ();
      if (m_virtual) assumptions.push_back(m_pred);
      lbool result = m_context.check (assumptions.size(), assumptions.c_ptr());
      if (m_virtual) assumptions.pop_back();
      return result;
    }

    void smt_context::get_model(model_ref& model) {
        m_context.get_model(model);
    }

    proof* smt_context::get_proof() {
        return m_context.get_proof();
    }

    smt_context_manager::smt_context_manager(smt_params& fp, unsigned max_num_contexts, ast_manager& m):
        m_fparams(fp), 
        m(m), 
        m_max_num_contexts(max_num_contexts),
        m_num_contexts(0) { m_stats.reset ();}
    
    
    smt_context_manager::~smt_context_manager() {
        TRACE("spacer",tout << "\n";);
        std::for_each(m_contexts.begin(), m_contexts.end(), delete_proc<smt::kernel>());
    }

    smt_context* smt_context_manager::mk_fresh() {        
        ++m_num_contexts;
        app_ref pred(m);
        smt::kernel * ctx = 0;
        if (m_max_num_contexts == 0) {
            m_contexts.push_back(alloc(smt::kernel, m, m_fparams));
            pred = m.mk_true();
            ctx = m_contexts[m_num_contexts-1];
        }
        else {
            if (m_contexts.size() < m_max_num_contexts) {
                m_contexts.push_back(alloc(smt::kernel, m, m_fparams));
            }
            std::stringstream name;
            name << "#context" << m_num_contexts;
            pred = m.mk_const(symbol(name.str().c_str()), m.mk_bool_sort());    
            ctx = m_contexts[(m_num_contexts-1)%m_max_num_contexts];
        }        
        return  alloc(smt_context, *ctx, *this, pred);   
    }

    void smt_context_manager::collect_statistics(statistics& st) const {
        for (unsigned i = 0; i < m_contexts.size(); ++i) {
            m_contexts[i]->collect_statistics(st);
        }
        st.update ("time.spacer.solve.smt.total", m_check_watch.get_seconds ());
        st.update ("spacer.smt_context_manager.checks", m_stats.m_num_smt_checks);
    }

    void smt_context_manager::reset_statistics() {
        for (unsigned i = 0; i < m_contexts.size(); ++i) {
            m_contexts[i]->reset_statistics();
        }
        m_stats.reset ();
        m_check_watch.reset ();
    }


};

