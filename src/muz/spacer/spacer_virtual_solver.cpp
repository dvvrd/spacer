#include "spacer_virtual_solver.h"
#include "ast_util.h"
#include "spacer_util.h"
#include "bool_rewriter.h"

#include "proof_checker.h"

namespace spacer {
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
        m_in_delay_scope (false),
        m_proof(m)
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
  
    namespace
    {
        static bool matches_fact (expr_ref_vector &args, expr* &match)
        {
            ast_manager &m = args.get_manager ();
            expr *fact = args.back ();
            for (unsigned i = 0, sz = args.size () - 1; i < sz; ++i)
            {
                expr *arg = args.get (i);
                if (m.is_proof (arg) &&
                    m.has_fact (to_app (arg)) &&
                    m.get_fact (to_app (arg)) == fact)
                {
                    match = arg;
                    return true;
                }
            }
            return false;
        }
    
    
        class elim_aux_assertions
        {
            app_ref m_aux;
        public:
            elim_aux_assertions (app_ref aux) : m_aux (aux) {}

            void mk_or_core (expr_ref_vector &args, expr_ref &res)
            {
                ast_manager &m = args.get_manager ();
                unsigned j = 0;
                for (unsigned i = 0, sz = args.size (); i < sz; ++i)
                {
                    if (m.is_false (args.get (i))) continue;
                    if (i != j) args [j] = args.get (i);
                    ++j;
                }
                res = m.mk_or (j, args.c_ptr ());
            }
      
            void mk_app (func_decl *decl, expr_ref_vector &args, expr_ref &res)
            {
                ast_manager &m = args.get_manager ();
                bool_rewriter brwr (m);

                if (decl->get_family_id () == m.get_basic_family_id () &&
                    decl->get_decl_kind () == OP_OR)
                    mk_or_core (args, res);
                else
                    brwr.mk_app (decl, args.size (), args.c_ptr (), res);
            }
      
            void operator() (ast_manager &m, proof *pr, proof_ref &res)
            {
                DEBUG_CODE(proof_checker pc(m);
                           expr_ref_vector side(m);
                           SASSERT(pc.check(pr, side));
                           );
                obj_map<app, app*> cache;
                bool_rewriter brwr (m);
        
                // for reference counting of new proofs
                app_ref_vector pinned(m);
        
                ptr_vector<app> todo;
                todo.push_back (pr);

                expr_ref not_aux(m);
                not_aux = m.mk_not (m_aux);
        
                expr_ref_vector args(m);

                while (!todo.empty ())
                {
                    app *p, *r;
                    expr *a;
          
                    p = todo.back ();
                    if (cache.find (pr, r))
                    {
                        todo.pop_back ();
                        continue;
                    }

                    SASSERT (!todo.empty () || pr == p);
                    bool dirty = false;
                    unsigned todo_sz = todo.size ();
                    args.reset ();
                    for (unsigned i = 0, sz = p->get_num_args (); i < sz; ++i)
                    {
                        expr* arg = p->get_arg (i);
                        if (arg == m_aux.get ())
                        {
                            dirty = true;
                            args.push_back (m.mk_true ());
                        }
                        else if (arg == not_aux.get ())
                        {
                            dirty = true;
                            args.push_back (m.mk_false ());
                        }
                        // skip (asserted m_aux)
                        else if (m.is_asserted (arg, a) && a == m_aux.get ())
                        {
                            dirty = true;
                        }
                        // skip (hypothesis m_aux)
                        else if (m.is_hypothesis (arg, a) && a == m_aux.get ())
                        {
                            dirty = true;
                        }
                        else if (is_app (arg) && cache.find (to_app (arg), r))
                        {
                            dirty |= (arg != r);
                            args.push_back (r);
                        }
                        else if (is_app (arg))
                            todo.push_back (to_app (arg));
                        else
                            // -- not an app
                            args.push_back (arg);
            
                    }
                    if (todo_sz < todo.size ()) 
                    {
                        // -- process parents
                        args.reset ();
                        continue;
                    }

                    // ready to re-create
                    app_ref newp(m);
                    if (!dirty) newp = p;
                    else if (m.is_unit_resolution (p))
                    {
                        if (args.size () == 2)
                            // unit resolution with m_aux that got collapsed to nothing
                            newp = to_app (args.get (0));
                        else
                        {
                            ptr_vector<proof> parents;
                            for (unsigned i = 0, sz = args.size () - 1; i < sz; ++i)
                                parents.push_back (to_app (args.get (i)));
                            SASSERT (parents.size () == args.size () - 1);
                            newp = m.mk_unit_resolution
                                (parents.size (), parents.c_ptr (), args.back ());
                            pinned.push_back (newp);
                        }
                    }
                    else if (matches_fact (args, a))
                    {
                        newp = to_app(a);
                    }
                    else
                    {
                        expr_ref papp (m);
                        mk_app (p->get_decl (), args, papp);
                        newp = to_app (papp.get ());
                        pinned.push_back (newp);
                    }
                    cache.insert (p, newp);
                    todo.pop_back ();
                    CTRACE("virtual",
                           p->get_decl_kind () == PR_TH_LEMMA &&
                           p->get_decl()->get_parameter (0).get_symbol () == "arith" &&
                           p->get_decl()->get_num_parameters() > 1 &&
                           p->get_decl()->get_parameter(1).get_symbol() == "farkas",
                           tout << "Old pf: " << mk_pp (p, m) << "\n"
                           << "New pf: " << mk_pp(newp, m) << "\n";);
                }
        
                proof *r;
                VERIFY (cache.find (pr,r));
        
                DEBUG_CODE(
                           proof_checker pc(m);
                           expr_ref_vector side(m);
                           SASSERT(pc.check(r, side));
                           );
        
                res = r ;
            }
        };
    }
  
    proof *virtual_solver::get_proof ()
    {
        scoped_watch _t_(m_factory.m_proof_watch);
    
        if (!m_proof.get ())
        {
            elim_aux_assertions pc (m_pred);
            m_proof = m_context.get_proof ();
            pc (m, m_proof.get (), m_proof);
        }
        return m_proof.get ();
    }
  
    bool virtual_solver::is_aux_predicate (expr *p)
    {return is_app (p) && to_app (p) == m_pred.get ();}
  
    lbool virtual_solver::check_sat_core (unsigned num_assumptions,
                                          expr *const * assumptions)
    {
        SASSERT (!m_pushed || get_scope_level () > 0);
        m_proof.reset ();
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
        name << "vsolver#" << m_num_solvers++;
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
        st.update ("time.virtual_solver.proof", m_proof_watch.get_seconds ());
        st.update ("virtual_solver.checks", m_stats.m_num_smt_checks);
        st.update ("virtual_solver.checks.sat", m_stats.m_num_sat_smt_checks);
    }
    void virtual_solver_factory::reset_statistics ()
    {
        m_context.reset_statistics ();
        m_stats.reset ();
        m_check_sat_watch.reset ();
        m_check_watch.reset ();
        m_proof_watch.reset ();
    }
  
  


  
}
