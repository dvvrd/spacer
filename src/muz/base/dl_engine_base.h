/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_engine_base.h

Abstract:

    Base class for Datalog engines.

Author:

    Nikolaj Bjorner (nbjorner) 2013-08-28

Revision History:

--*/
#ifndef _DL_ENGINE_BASE_H_
#define _DL_ENGINE_BASE_H_

#include "model.h"
#include "dl_util.h"

namespace datalog {
    enum DL_ENGINE {
        DATALOG_ENGINE,
        PDR_ENGINE,
        SPACER_ENGINE,
        QPDR_ENGINE,
        BMC_ENGINE,
        QBMC_ENGINE,
        TAB_ENGINE,
        CLP_ENGINE,
	DUALITY_ENGINE,
        DDNF_ENGINE,
        LAST_ENGINE
    };

    class engine_base {
        ast_manager& m;
        std::string m_name;
    public:
        engine_base(ast_manager& m, char const* name): m(m), m_name(name) {}
        virtual ~engine_base() {}

        virtual expr_ref get_answer() = 0;
        virtual expr_ref get_ground_sat_answer () {
            throw default_exception(std::string("operation is not supported for ") + m_name);
        }
        virtual lbool query(expr* q) = 0;
        virtual lbool query(unsigned num_rels, func_decl*const* rels) { return l_undef; }
        virtual lbool query_from_lvl (expr* q, unsigned lvl) {
            throw default_exception(std::string("operation is not supported for ") + m_name);
        }
        
        /*************************************************************/
        //-- begin methods added for PSMC. we did not make them pure
        //-- virtual since there are many other classes (e.g.,
        //-- duality) that extend this class and they would not
        //-- necessarily implement these methods. instead an error
        //-- message will be printed and l_undef will be returned,
        //-- which will trigger exception handling up the call chain.
        /*************************************************************/

        virtual lbool prepare_query(expr* q) { 
          std::cout << "ERROR: prepare_query not implemented !!\n";
          return l_undef; 
        }

        virtual lbool init_root() { 
          std::cout << "ERROR: init_root not implemented !!\n";
          return l_undef; 
        }

        virtual lbool check_reachability() { 
          std::cout << "ERROR: check_reachability not implemented !!\n";
          return l_undef; 
        }

        /*************************************************************/
        //-- end methods added for PSMC
        /*************************************************************/


        virtual void reset_statistics() {}
        virtual void display_profile(std::ostream& out) const {}
        virtual void collect_statistics(statistics& st) const {}
        virtual unsigned get_num_levels(func_decl* pred) {
            throw default_exception(std::string("get_num_levels is not supported for ") + m_name);
        }
        virtual expr_ref get_cover_delta(int level, func_decl* pred) {
            throw default_exception(std::string("operation is not supported for ") + m_name);
        }
        virtual void add_cover(int level, func_decl* pred, expr* property) {
            throw default_exception(std::string("operation is not supported for ") + m_name);
        }
        virtual void display_certificate(std::ostream& out) const {
            throw default_exception(std::string("certificates are not supported for ") + m_name);
        }
        virtual model_ref get_model() {
            return model_ref(alloc(model, m));
        }
        virtual void get_rules_along_trace (rule_ref_vector& rules) {
            throw default_exception(std::string("get_rules_along_trace is not supported for ") + m_name);
        }
        virtual proof_ref get_proof() {
            return proof_ref(m.mk_asserted(m.mk_true()), m);
        }
        virtual void updt_params() {}
        virtual void cancel() {}
        virtual void cleanup() {}
    };

    class context;

    class register_engine_base {
    public:
        virtual engine_base* mk_engine(DL_ENGINE engine_type) = 0;
        virtual void set_context(context* ctx) = 0;
    };
}

#endif
