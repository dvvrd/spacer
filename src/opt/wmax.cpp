/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    wmax.cpp

Abstract:

    Theory based MaxSAT.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/
#include "wmax.h"
#include "uint_set.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"
#include "smt_theory.h"
#include "smt_context.h"
#include "theory_wmaxsat.h"


namespace opt {
    class maxsmt_solver_wbase : public maxsmt_solver_base {
        smt::context& ctx;
    public:
        maxsmt_solver_wbase(opt_solver* s, ast_manager& m, smt::context& ctx, params_ref& p, 
                            vector<rational> const& ws, expr_ref_vector const& soft): 
            maxsmt_solver_base(s, m, p, ws, soft), ctx(ctx) {}
        ~maxsmt_solver_wbase() {}

        class scoped_ensure_theory {
            smt::theory_wmaxsat* m_wth;
        public:
            scoped_ensure_theory(maxsmt_solver_wbase& s) {
                m_wth = s.ensure_theory();
            }
            ~scoped_ensure_theory() {
                m_wth->reset();
            }
            smt::theory_wmaxsat& operator()() { return *m_wth; }
        };
        
        smt::theory_wmaxsat* ensure_theory() {
            smt::theory_wmaxsat* wth = get_theory();
            if (wth) {
                wth->reset();
            }
            else {
                wth = alloc(smt::theory_wmaxsat, m, m_mc);
                ctx.register_plugin(wth);
            }
            return wth;
        }
        smt::theory_wmaxsat* get_theory() const {
            smt::theory_id th_id = m.get_family_id("weighted_maxsat");
            smt::theory* th = ctx.get_theory(th_id);               
            if (th) {
                return dynamic_cast<smt::theory_wmaxsat*>(th);
            }
            else {
                return 0;
            }
        }
    };

    // ----------------------------------------------------------
    // weighted max-sat using a custom theory solver for max-sat.
    // NB. it is quite similar to pseudo-Boolean propagation.


    class wmax : public maxsmt_solver_wbase {
    public:
        wmax(opt_solver* s, ast_manager& m, smt::context& ctx, params_ref& p, 
             vector<rational> const& ws, expr_ref_vector const& soft): 
            maxsmt_solver_wbase(s, m, ctx, p, ws, soft) {}
        virtual ~wmax() {}

        lbool operator()() {
            TRACE("opt", tout << "weighted maxsat\n";);
            scoped_ensure_theory wth(*this);
            solver::scoped_push _s(s());
            lbool is_sat = l_true;
            bool was_sat = false;
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                wth().assert_weighted(m_soft[i].get(), m_weights[i]);
            }
            solver::scoped_push __s(s());
            while (l_true == is_sat) {
                IF_VERBOSE(1, verbose_stream() << "(opt.wmax [" << m_lower << ":" << m_upper << "])\n";);
                is_sat = s().check_sat(0,0);
                if (m_cancel) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    if (wth().is_optimal()) {
                        m_upper = wth().get_min_cost();
                        s().get_model(m_model);
                    }
                    expr_ref fml = wth().mk_block();
                    s().assert_expr(fml);
                    was_sat = true;
                }
            }
            if (was_sat) {
                wth().get_assignment(m_assignment);
            }
            if (is_sat == l_false && was_sat) {
                is_sat = l_true;
            }
            m_upper = wth().get_min_cost();
            if (is_sat == l_true) {
                m_lower = m_upper;
            }
            TRACE("opt", tout << "min cost: " << m_upper << "\n";);
            return is_sat;
        }
    };

    maxsmt_solver_base* opt::mk_wmax(ast_manager& m, opt_solver* s, params_ref& p, 
                                    vector<rational> const& ws, expr_ref_vector const& soft) {
        return alloc(wmax, s, m, s->get_context(), p, ws, soft);
    }

}