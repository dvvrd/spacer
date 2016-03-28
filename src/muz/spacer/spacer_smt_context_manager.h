/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_smt_context_manager.h

Abstract:

    Manager of smt contexts

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-26.

Revision History:

--*/

#ifndef _SPACER_SMT_CONTEXT_MANAGER_H_
#define _SPACER_SMT_CONTEXT_MANAGER_H_

#include "smt_kernel.h"
#include "func_decl_dependencies.h"
#include "dl_util.h"
#include "spacer_virtual_solver.h"
#include "stopwatch.h"

namespace spacer {
    
    class smt_context_manager {
      
      struct stats {
        unsigned m_num_smt_checks;
        unsigned m_num_sat_smt_checks;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
      };
          
        smt_params&              m_fparams;
        ast_manager&             m;
        unsigned                 m_max_num_contexts;
        ptr_vector<virtual_solver_factory> m_solvers;
        unsigned                 m_num_contexts;
        

        stats     m_stats;
        stopwatch m_check_watch;
        stopwatch m_check_sat_watch;
      
    public:
        smt_context_manager(smt_params& fp, unsigned max_num_contexts, ast_manager& m);
        ~smt_context_manager();
        virtual_solver* mk_fresh();                
        void collect_statistics(statistics& st) const;
        void reset_statistics();

      friend class smt_context;
    };

};

#endif
