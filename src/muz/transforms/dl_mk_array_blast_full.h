/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_array_blast_full.h

Abstract:

    Remove array variables from rules using QE of array variables

Author:

    Anvesh Komuravelli
    (Based on dl_mk_array_blast)

Revision History:

--*/
#ifndef _DL_MK_ARRAY_BLAST_FULL_H_
#define _DL_MK_ARRAY_BLAST_FULL_H_

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"
#include"dl_mk_interp_tail_simplifier.h"
#include "equiv_proof_converter.h"
#include "array_decl_plugin.h"

namespace datalog {

    /**
       \brief Blast occurrences of arrays in rules
    */
    class mk_array_blast_full : public rule_transformer::plugin {
        typedef obj_map<app, var*> defs_t;

        context&                    m_ctx;
        ast_manager&                m;
        array_util                  m_a;
        rule_manager&               m_rm;
        params_ref                  m_params;
        th_rewriter                 m_rewriter;
        mk_interp_tail_simplifier   m_simplifier;

        bool blast(rule& r, rule_set& new_rules);

    public:
        /**
           \brief Create rule transformer that removes array stores and selects by ackermannization.
        */
        mk_array_blast_full (context & ctx, unsigned priority);

        virtual ~mk_array_blast_full ();
        
        rule_set * operator()(rule_set const & source);

    };

};

#endif /* _DL_MK_ARRAY_BLAST_FULL_H_ */

