/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_rule_set.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-17.

Revision History:

--*/

#include<algorithm>
#include<functional>
#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_dependencies.h"
#include"ast_pp.h"

namespace datalog {

    rule_set::rule_set(context & ctx) 
          : m_context(ctx), 
            m_rule_manager(ctx.get_rule_manager()), 
            m_rules(m_rule_manager), 
            m_deps(alloc(rule_dependencies, ctx)),
            m_stratifier(0), 
            m_refs(ctx.get_manager()) {
    }

    rule_set::rule_set(const rule_set & other) 
        : m_context(other.m_context), 
          m_rule_manager(other.m_rule_manager), 
          m_rules(m_rule_manager),
          m_deps(alloc(rule_dependencies, other.m_context)),
          m_stratifier(0),
          m_refs(m_context.get_manager()) {
        add_rules(other);
        if (other.m_stratifier) {
            VERIFY(close());
        }
    }

    rule_set::~rule_set() {
        reset();
    }

    void rule_set::reset() {
        m_rules.reset();
        reset_dealloc_values(m_head2rules);
        m_deps->reset();
        m_stratifier = 0;
        m_output_preds.reset();
        m_orig2pred.reset();
        m_pred2orig.reset();
        m_refs.reset();
    }

    ast_manager & rule_set::get_manager() const {
        return m_context.get_manager();
    }

    func_decl* rule_set::get_orig(func_decl* pred) const {
        func_decl* orig = pred;
        m_pred2orig.find(pred, orig);
        return orig;
    }

    func_decl* rule_set::get_pred(func_decl* orig) const {
        func_decl* pred = orig;
        m_orig2pred.find(orig, pred);
        return pred;
    }

    void rule_set::inherit_predicates(rule_set const& other) {
        m_refs.append(other.m_refs);
        set_union(m_output_preds, other.m_output_preds);
        {
            obj_map<func_decl, func_decl*>::iterator it = other.m_orig2pred.begin();
            obj_map<func_decl, func_decl*>::iterator end = other.m_orig2pred.end();
            for (; it != end; ++it) {
                m_orig2pred.insert(it->m_key, it->m_value);
            }
        }
        {
            obj_map<func_decl, func_decl*>::iterator it = other.m_pred2orig.begin();
            obj_map<func_decl, func_decl*>::iterator end = other.m_pred2orig.end();
            for (; it != end; ++it) {
                m_pred2orig.insert(it->m_key, it->m_value);
            }
        }
    }

    void rule_set::inherit_predicate(rule_set const& other, func_decl* orig, func_decl* pred) {
        if (other.is_output_predicate(orig)) {
            set_output_predicate(pred);
        }
        orig = other.get_orig(orig);
        m_refs.push_back(pred);
        m_refs.push_back(orig);
        m_orig2pred.insert(orig, pred);
        m_pred2orig.insert(pred, orig);
    }

    void rule_set::add_rule(rule * r) {
        TRACE("dl_verbose", r->display(m_context, tout << "add:"););
        SASSERT(!is_closed());
        m_rules.push_back(r);
        app * head = r->get_head();
        SASSERT(head != 0);
        func_decl * d = head->get_decl();
        decl2rules::obj_map_entry* e = m_head2rules.insert_if_not_there2(d, 0);
        if (!e->get_data().m_value) e->get_data().m_value = alloc(ptr_vector<rule>);
        e->get_data().m_value->push_back(r);
    }

    void rule_set::del_rule(rule * r) {
        TRACE("dl", r->display(m_context, tout << "del:"););
        func_decl* d = r->get_decl();
        rule_vector* rules = m_head2rules.find(d);
#define DEL_VECTOR(_v)                                  \
        for (unsigned i = (_v).size(); i > 0; ) {       \
            --i;                                        \
            if ((_v)[i] == r) {                         \
                (_v)[i] = (_v).back();                  \
                (_v).pop_back();                        \
                break;                                  \
            }                                           \
        }                                               \
        
        DEL_VECTOR(*rules);
        DEL_VECTOR(m_rules);
    }    

    void rule_set::replace_rule(rule * r, rule * other) {
        TRACE("dl", r->display(m_context, tout << "replace:"););
        func_decl* d = r->get_decl();
        rule_vector* rules = m_head2rules.find(d);
#define REPLACE_VECTOR(_v)                              \
        for (unsigned i = (_v).size(); i > 0; ) {       \
            --i;                                        \
            if ((_v)[i] == r) {                         \
                (_v)[i] = other;                        \
                break;                                  \
            }                                           \
        }                                               \

        REPLACE_VECTOR(*rules);
        REPLACE_VECTOR(m_rules);
    }

    void rule_set::ensure_closed() {
        if (!is_closed()) {
            VERIFY(close());
        }
    }

    bool rule_set::close() {
        SASSERT(!is_closed()); //the rule_set is not already closed        
        m_deps->populate(*this);
        m_stratifier = alloc(rule_stratifier, *m_deps);
        if (!stratified_negation()) {
            m_stratifier = 0;
            m_deps->reset();
            return false;
        }
        return true;
    }

    void rule_set::reopen() {
        if (is_closed()) {
            m_stratifier = 0;
            m_deps->reset();
        }
    }

    /**
       \brief Return true if the negation is indeed stratified.
    */
    bool rule_set::stratified_negation() {
        ptr_vector<rule>::const_iterator it  = m_rules.c_ptr();
        ptr_vector<rule>::const_iterator end = m_rules.c_ptr()+m_rules.size();
        for (; it != end; it++) {
            rule * r = *it;
            app * head = r->get_head();
            func_decl * head_decl = head->get_decl();
            unsigned n = r->get_uninterpreted_tail_size();
            for (unsigned i = r->get_positive_tail_size(); i < n; i++) {
                SASSERT(r->is_neg_tail(i));
                func_decl * tail_decl = r->get_tail(i)->get_decl();
                unsigned neg_strat = get_predicate_strat(tail_decl);
                unsigned head_strat = get_predicate_strat(head_decl);

                SASSERT(head_strat>=neg_strat); //head strat can never be lower than that of a tail
                if (head_strat == neg_strat) {
                    return false;
                }
            }
        }
        return true;
    }


    void rule_set::replace_rules(const rule_set & src) {
        if (this != &src) {
            reset();
            add_rules(src);
        }
    }

    void rule_set::add_rules(const rule_set & src) {
        SASSERT(!is_closed());
        unsigned n = src.get_num_rules();
        for (unsigned i = 0; i < n; i++) {
            add_rule(src.get_rule(i));
        }
        inherit_predicates(src);
    }

    const rule_vector & rule_set::get_predicate_rules(func_decl * pred) const { 
        decl2rules::obj_map_entry * e = m_head2rules.find_core(pred);
        if (!e) {
            return m_empty_rule_vector;
        }
        return *e->get_data().m_value;
    }

    const rule_set::pred_set_vector & rule_set::get_strats() const {
        SASSERT(m_stratifier);
        return m_stratifier->get_strats();
    }

    unsigned rule_set::get_predicate_strat(func_decl * pred) const {
        SASSERT(m_stratifier);
        return m_stratifier->get_strat(pred);
    }

    void rule_set::split_founded_rules(func_decl_set& founded, func_decl_set& non_founded) {
        founded.reset();
        non_founded.reset();
        {
            decl2rules::iterator it = begin_grouped_rules(), end = end_grouped_rules();
            for (; it != end; ++it) {
                non_founded.insert(it->m_key);
            }
        }
        bool change = true;
        while (change) {
            change = false;
            func_decl_set::iterator it = non_founded.begin(), end = non_founded.end();
            for (; it != end; ++it) {
                rule_vector const& rv = get_predicate_rules(*it);
                bool found = false;
                for (unsigned i = 0; !found && i < rv.size(); ++i) {
                    rule const& r = *rv[i];
                    bool is_founded = true;
                    for (unsigned j = 0; is_founded && j < r.get_uninterpreted_tail_size(); ++j) {
                        is_founded = founded.contains(r.get_decl(j));
                    }
                    if (is_founded) {
                        founded.insert(*it);
                        non_founded.remove(*it);
                        change = true;
                        found  = true;
                    }
                }
            }
        }
    }

    void rule_set::display(std::ostream & out) const {
        out << "; rule count: " << get_num_rules() << "\n";
        out << "; predicate count: " << m_head2rules.size() << "\n";
        func_decl_set::iterator pit = m_output_preds.begin();
        func_decl_set::iterator pend = m_output_preds.end();
        for (; pit != pend; ++pit) {
            out << "; output: " << (*pit)->get_name() << '\n';
        }
        decl2rules::iterator it  = m_head2rules.begin();
        decl2rules::iterator end = m_head2rules.end();
        for (; it != end; ++it) {
            ptr_vector<rule> * rules = it->m_value;
            ptr_vector<rule>::iterator it2  = rules->begin();
            ptr_vector<rule>::iterator end2 = rules->end();
            for (; it2 != end2; ++it2) {
                rule * r = *it2;
                if (!r->passes_output_thresholds(m_context)) {
                    continue;
                }
                r->display(m_context, out);
            }
        }
    }


    void rule_set::display_deps( std::ostream & out ) const
    {
        const pred_set_vector & strats = get_strats();
        pred_set_vector::const_iterator sit = strats.begin();
        pred_set_vector::const_iterator send = strats.end();
        for (; sit!=send; ++sit) {
            func_decl_set & strat = **sit;
            func_decl_set::iterator fit=strat.begin();
            func_decl_set::iterator fend=strat.end();
            bool non_empty = false;
            for (; fit!=fend; ++fit) {
                func_decl * first = *fit;
                const func_decl_set & deps = m_deps->get_deps(first);
                func_decl_set::iterator dit=deps.begin();
                func_decl_set::iterator dend=deps.end();
                for (; dit!=dend; ++dit) {
                    non_empty = true;
                    func_decl * dep = *dit;
                    out<<first->get_name()<<" -> "<<dep->get_name()<<"\n";
                }
            }
            if (non_empty && sit!=send) {
                out << "\n";
            }
        }
    }

};
