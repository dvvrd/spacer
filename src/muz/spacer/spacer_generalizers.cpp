/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_generalizers.cpp

Abstract:

    Generalizers of satisfiable states and unsat cores.

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-20.

Revision History:

--*/


#include "spacer_context.h"
#include "spacer_farkas_learner.h"
#include "spacer_generalizers.h"
#include "expr_abstract.h"
#include "var_subst.h"
#include "for_each_expr.h"
#include "obj_equiv_class.h"


namespace
{
  inline expr_equiv_class remove_eq_conds_tmp(expr_ref_vector& e)
  {
    ast_manager& m = e.get_manager();
    arith_util m_a(m);
    expr_equiv_class eq_classes(m);
    flatten_and(e);
    expr_ref_vector res(m);
    for(unsigned i=0;i<e.size();i++)
    {
      expr*e1, *e2;
      if(m.is_eq(e[i].get(), e1, e2))	
      {
        if(m_a.is_add(e1) && e2 == m_a.mk_int(0))
        {
          app* f = to_app(e1);
          expr*first=f->get_arg(0);
          expr*snd=f->get_arg(1);
          if(m_a.is_mul(snd))
          {
            app*mult=to_app(snd);
            if(m_a.is_minus_one(mult->get_arg(0)))
            {
              e1 = first; e2=mult->get_arg(1);
            }
          }
        } 
        eq_classes.merge(e1, e2);
      }
      else
        res.push_back(e[i].get());
    }
    e.reset();
    e.append(res);
    return eq_classes;
  }
}

namespace spacer {


    // ------------------------
    // core_bool_inductive_generalizer

    // main propositional induction generalizer.
    // drop literals one by one from the core and check if the core is still inductive.
    //    
    void core_bool_inductive_generalizer::operator()(model_node& n, expr_ref_vector& core, unsigned& uses_level) {
        m_st.count++;
        scoped_watch _w_(m_st.watch);
        if (core.size() <= 1) {
            return;
        }
        ast_manager& m = core.get_manager();
        TRACE("spacer", for (unsigned i = 0; i < core.size(); ++i) { tout << mk_pp(core[i].get(), m) << "\n"; });
        unsigned num_failures = 0, i = 0, old_core_size = core.size();
        ptr_vector<expr> processed;

        while (i < core.size() && 1 < core.size() && (!m_failure_limit || num_failures <= m_failure_limit)) {
            expr_ref lit(m);
            lit = core[i].get();
            core[i] = m.mk_true();            
            if (n.pt().check_inductive(n.level(), core, uses_level)) {
                num_failures = 0;
                for (i = 0; i < core.size() && processed.contains(core[i].get()); ++i);
            }
            else {
                core[i] = lit;
                processed.push_back(lit);
                ++num_failures;
                ++i;
            }
        }
        IF_VERBOSE(2, verbose_stream() << "old size: " << old_core_size << " new size: " << core.size() << "\n";);
        TRACE("spacer", tout << "old size: " << old_core_size << " new size: " << core.size() << "\n";);
    }
  void core_bool_inductive_generalizer::collect_statistics (statistics &st) const
  {
    st.update ("time.spacer.solve.reach.gen.bool_ind", m_st.watch.get_seconds ());
    st.update ("bool inductive gen", m_st.count);
  }
  
  namespace
  {
    class collect_array_proc 
    {
      array_util m_au;
      func_decl_set &m_symbs;
      sort *m_sort;
    public:
      collect_array_proc (ast_manager &m, func_decl_set& s) : 
        m_au (m), m_symbs (s), m_sort(NULL) {}
      
      void operator() (app* a)
      {
        if (a->get_family_id () == null_family_id && m_au.is_array (a))
        {
          if (m_sort && m_sort != get_sort (a)) return;
          if (!m_sort) m_sort = get_sort (a);
          m_symbs.insert (a->get_decl ());
        }
      }
      void operator() (var*) {}
      void operator() (quantifier*) {}
    };
  }
  
  void core_array_eq_generalizer::operator() 
    (model_node &n, expr_ref_vector& core, unsigned &uses_level)
  {
    TRACE ("core_array_eq", tout << "Looking for equalities\n";);
    
    // -- find array constants
    ast_manager &m = m_ctx.get_ast_manager ();
    manager &pm = m_ctx.get_manager ();
    
    expr_ref v(m);
    v = pm.mk_and (core);
    func_decl_set symb;
    collect_array_proc cap (m, symb);
    for_each_expr (cap, v);
    
    TRACE ("core_array_eq", 
           tout << "found " << symb.size () << " array variables in: \n"
           << mk_pp (v, m) << "\n";);
    
    // too few constants
    if (symb.size () <= 1) return;
    // too many constants, skip this
    if (symb.size () >= 8) return;
    
    
    // -- for every pair of variables, try an equality
    typedef func_decl_set::iterator iterator;
    ptr_vector<func_decl> vsymbs;
    for (iterator it = symb.begin (), end = symb.end (); 
         it != end; ++it)
      vsymbs.push_back (*it);
    
    expr_ref_vector eqs (m);
    
    for (unsigned i = 0, sz = vsymbs.size (); i < sz; ++i)
      for (unsigned j = i + 1; j < sz; ++j)
        eqs.push_back (m.mk_eq (m.mk_const (vsymbs.get (i)), m.mk_const (vsymbs.get (j))));
    
    smt::kernel solver (m, m_ctx.get_manager().fparams2 ());
    expr_ref_vector lits (m);
    for (unsigned i = 0, core_sz = core.size (); i < core_sz; ++i)
    {
      SASSERT (lits.size () == i);
      solver.push ();
      solver.assert_expr (core.get (i));
      for (unsigned j = 0, eqs_sz = eqs.size (); j < eqs_sz; ++j)
      {
        solver.push ();
        solver.assert_expr (eqs.get (j));
        lbool res = solver.check ();
        solver.pop (1);
        
        if (res == l_false)
        {  
          TRACE ("core_array_eq", 
                 tout << "strengthened " << mk_pp (core.get (i), m)
                 << " with " << mk_pp (m.mk_not (eqs.get (j)), m) << "\n";);
          lits.push_back (m.mk_not (eqs.get (j)));
          break;
        }
      }
      solver.pop (1);
      if (lits.size () == i) lits.push_back (core.get (i));
    }
    
    /**
       HACK: if the first 3 arguments of pt are boolean, assume
       they correspond to SeaHorn encoding and condition the equality on them.
    */
    // pred_transformer &pt = n.pt ();
    // if (pt.sig_size () >= 3 &&
    //     m.is_bool (pt.sig (0)->get_range ()) &&
    //     m.is_bool (pt.sig (1)->get_range ()) &&
    //     m.is_bool (pt.sig (2)->get_range ()))
    // {
    //   lits.push_back (m.mk_const (pm.o2n(pt.sig (0), 0))); 
    //   lits.push_back (m.mk_not (m.mk_const (pm.o2n(pt.sig (1), 0))));
    //   lits.push_back (m.mk_not (m.mk_const (pm.o2n(pt.sig (2), 0))));
    // }
          
    TRACE ("core_array_eq", tout << "new possible core " 
           << mk_pp (pm.mk_and (lits), m) << "\n";);
    
          
    // -- check if it is consistent with the transition relation
    unsigned uses_level1;
    if (n.pt ().check_inductive (n.level (), lits, uses_level1))
    {
      TRACE ("core_array_eq", tout << "Inductive!\n";);
      core.reset ();
      core.append (lits);
      uses_level = uses_level1;
      return;
    }
    else
    { TRACE ("core_array_eq", tout << "Not-Inductive!\n";);}
  }

  void core_eq_generalizer::operator() 
    (model_node &n, expr_ref_vector& core, unsigned &uses_level)
  {
    TRACE ("core_eq", tout << "Transforming equivalence classes\n";);
    
    ast_manager &m = m_ctx.get_ast_manager ();
    expr_equiv_class eq_classes(remove_eq_conds_tmp(core));
    for(expr_equiv_class::equiv_iterator eq_c = eq_classes.begin(); eq_c!=eq_classes.end();++eq_c)
    {
      unsigned nb_elem=0;
      for(expr_equiv_class::iterator a = (*eq_c).begin(); a!=(*eq_c).end();++a)
      {
        nb_elem++;
        expr_equiv_class::iterator b(a);
        for(++b; b!=(*eq_c).end();++b)
        {
          core.push_back(m.mk_eq(*a, *b));
        }
      }
    }
  }
};
