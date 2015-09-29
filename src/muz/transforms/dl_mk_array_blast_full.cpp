/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_array_blast_full.cpp

Abstract:

    Remove array variables from rules using QE of array variables

Author:

    Anvesh Komuravelli
    (Based on dl_mk_array_blast)

Revision History:

--*/

#include "dl_mk_array_blast_full.h"
#include "qe_array.h"
#include "scoped_proof.h"

namespace datalog {


    mk_array_blast_full::mk_array_blast_full(context & ctx, unsigned priority) : 
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()), 
        m_a(m),
        m_rm(ctx.get_rule_manager()),
        m_rewriter(m, m_params),
        m_simplifier(ctx)
    { }

    mk_array_blast_full::~mk_array_blast_full() { }

    bool mk_array_blast_full::blast(rule& r, rule_set& rules) {
        TRACE("dl", r.display(m_ctx, tout << "old rule\n"););

        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz = r.get_tail_size();
        expr_ref_vector conjs(m), new_conjs(m);
        expr_ref it_tail (m);
        qe_array qea (m);

        uint_set ut_vars; // vars used in uninterpreted part of the tail
        uint_set tail_vars = m_rm.collect_tail_vars (&r);
        UNREACHABLE ();
       /** XXX get_var_sorts() is no longer defined 
        ptr_vector<sort> tail_var_sorts (m_rm.get_var_sorts ());
        */
        ptr_vector<sort> tail_var_sorts;
        

        for (unsigned i = 0; i < utsz; ++i) {
            expr *t = r.get_tail (i);
            new_conjs.push_back(t);
            ut_vars |= m_rm.collect_vars (t);
        }
        for (unsigned i = utsz; i < tsz; ++i) {
            expr *t = r.get_tail (i);
            conjs.push_back(t);
        }
        it_tail = m.mk_and (conjs.size (), conjs.c_ptr ()); // interpreted part of tail

        TRACE ("dl",
                tout << "interpreted part of tail:\n";
                tout << mk_pp (it_tail, m) << "\n";
              );

        // head vars
        expr_ref head (r.get_head(), m);
        uint_set head_vars = m_rm.collect_vars (head);
        UNREACHABLE();
        /** XXX get_var_sorts() is no longer defined 
            unsigned num_head_vars = m_rm.get_var_sorts ().size (); */
        unsigned num_head_vars = 0;
        

        // num_tail_vars and num_vars
        unsigned num_tail_vars = tail_var_sorts.size ();
        unsigned num_vars = (num_head_vars > num_tail_vars) ? num_head_vars : num_tail_vars;

        // eliminate array vars in (tail_vars - ut_vars - head_vars)
        uint_set arr_vars;
        for (unsigned idx = 0; idx < num_tail_vars; idx++) {
            sort* s = tail_var_sorts.get (idx);
            if (s && m_a.is_array (s) && !ut_vars.contains (idx) && !head_vars.contains (idx)) {
                arr_vars.insert (idx);
                TRACE ("dl",
                        tout << "array var to eliminate: " << idx << "\n";
                      );
            }
        }

        TRACE ("dl",
                tout << "number of vars in the rule: " << num_vars << "\n";
              );

        expr_ref old_it_tail (it_tail, m);
        qea (arr_vars, it_tail, num_vars);
        TRACE ("dl",
                tout << "interpreted tail after QE: \n";
                tout << mk_pp (it_tail, m) << "\n";
              );
        if (old_it_tail == it_tail) {
            rules.add_rule (&r);
            return false;
        }

        expr_ref body (m), fml1 (m), fml2 (m);

        // new body
        new_conjs.push_back (it_tail);
        qe::flatten_and (new_conjs);
        body = m.mk_and(new_conjs.size(), new_conjs.c_ptr());
        m_rewriter(body);

        TRACE ("dl",
                tout << "new body: \n";
                tout << mk_pp (body, m) << "\n";
              );

        // new rule
        fml2 = m.mk_implies(body, head);
        proof_ref p(m);
        rule_set new_rules(m_ctx);
        m_rm.mk_rule(fml2, p, new_rules, r.name());

        // add the new rule if necessary
        rule_ref new_rule(m_rm);
        if (m_simplifier.transform_rule(new_rules.last(), new_rule)) {
            if (r.get_proof()) {
                scoped_proof _sc(m);
                m_rm.to_formula(r, fml1);
                p = m.mk_rewrite(fml1, fml2);
                p = m.mk_modus_ponens(r.get_proof(), p);
                new_rule->set_proof(m, p);                
            }
            rules.add_rule(new_rule);
            m_rm.mk_rule_rewrite_proof(r, *new_rule.get());
            TRACE("dl", new_rule->display(m_ctx, tout << "new rule\n"););
        }
        else {
            TRACE ("dl", tout << "rule dropped\n";);
        }
        return true;
    }
    
    rule_set * mk_array_blast_full::operator()(rule_set const & source) {
        if (!m_ctx.array_blast_full ()) {
            return 0;
        }
        rule_set* rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);
        rule_set::iterator it = source.begin(), end = source.end();
        bool change = false;
        for (; !m_ctx.canceled() && it != end; ++it) {
            change = blast(**it, *rules) || change;
        }
        if (!change) {
            dealloc(rules);
            rules = 0;
        }        
        return rules;        
    }

};
