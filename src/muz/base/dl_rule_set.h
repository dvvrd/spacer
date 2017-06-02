/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_rule_set.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-17.

Revision History:

--*/
#ifndef DL_RULE_SET_H_
#define DL_RULE_SET_H_

#include"obj_hashtable.h"
#include"dl_rule.h"

namespace datalog {

    template<typename T>
    class rule_dependencies_base;
    class rule_dependencies;
    class rule_stratifier;

    /**
       \brief Datalog "Program" (aka rule set).
    */
    class rule_set {
    public:
        typedef ptr_vector<func_decl_set> pred_set_vector;
        typedef obj_map<func_decl, rule_vector*> decl2rules;
    private:
        typedef obj_map<func_decl, func_decl_set*> decl2deps;

        context &                     m_context;
        rule_manager &                m_rule_manager;
        rule_ref_vector               m_rules;        //!< all rules
        decl2rules                    m_head2rules;   //!< mapping from head symbol to rules.
        scoped_ptr<rule_dependencies> m_deps;         //!< dependencies
        scoped_ptr<rule_stratifier>   m_stratifier;   //!< contains stratifier object iff the rule_set is closed
        func_decl_set                 m_output_preds; //!< output predicates
        obj_map<func_decl,func_decl*> m_orig2pred;
        obj_map<func_decl,func_decl*> m_pred2orig;
        func_decl_ref_vector          m_refs;


        //sometimes we need to return reference to an empty rule_vector,
        //so we return reference to this one.
        rule_vector                  m_empty_rule_vector;

        void compute_deps();
        void compute_tc_deps();
        bool stratified_negation();
    public:
        rule_set(context & ctx);
        rule_set(const rule_set & rs);
        ~rule_set();

        ast_manager & get_manager() const;
        rule_manager & get_rule_manager() const { return const_cast<rule_manager&>(m_rule_manager); }
        context&  get_context() const { return m_context; }


        void inherit_predicates(rule_set const& other);
        void inherit_predicate(rule_set const& other, func_decl* orig, func_decl* pred);
        func_decl* get_orig(func_decl* pred) const;
        func_decl* get_pred(func_decl* orig) const;

        /**
           \brief Add rule \c r to the rule set.
        */
        void add_rule(rule * r);

        /**
           \brief Remove rule \c r from the rule set.
        */
        void del_rule(rule * r);

        /**
           \brief Add all rules from a different rule_set.
        */
        void add_rules(const rule_set& src);
        void replace_rules(const rule_set& other);
        void replace_rule(rule * r, rule * other);

        /**
           \brief This method should be invoked after all rules are added to the rule set.
           It will check if the negation is indeed stratified.
           Return true if succeeded.

           \remark If new rules are added, the rule_set will be "reopen".
        */
        bool close();
        void ensure_closed();
        /**
           \brief Undo the effect of the \c close() operation.
         */
        void reopen();
        bool is_closed() const { return m_stratifier != 0; }

        unsigned get_num_rules() const { return m_rules.size(); }
        bool empty() const { return m_rules.size() == 0; }

        rule * get_rule(unsigned i) const { return m_rules[i]; }
        rule * last() const { return m_rules[m_rules.size()-1]; }
        rule_ref_vector const& get_rules() const { return m_rules; }

        const rule_vector & get_predicate_rules(func_decl * pred) const;
        bool contains(func_decl* pred) const { return m_head2rules.contains(pred); }

        const rule_stratifier & get_stratifier() const {
            SASSERT(m_stratifier);
            return *m_stratifier;
        }
        const pred_set_vector & get_strats() const;
        unsigned get_predicate_strat(func_decl * pred) const;
        const rule_dependencies & get_dependencies() const { SASSERT(is_closed()); return *m_deps; }

        // split predicats into founded and non-founded.
        void split_founded_rules(func_decl_set& founded, func_decl_set& non_founded);

        void reset();

        void set_output_predicate(func_decl * pred) { m_refs.push_back(pred); m_output_preds.insert(pred); }
        bool is_output_predicate(func_decl * pred) const { return m_output_preds.contains(pred); }
        const func_decl_set & get_output_predicates() const { return m_output_preds; }
        func_decl* get_output_predicate() const { SASSERT(m_output_preds.size() == 1); return *m_output_preds.begin(); }


        void display(std::ostream & out) const;

        /**
           \brief Output rule dependencies.

           The rule set must be closed before calling this function.
         */
        void display_deps(std::ostream & out) const;

        typedef rule * const * iterator;
        iterator begin() const { return m_rules.c_ptr(); }
        iterator end() const { return m_rules.c_ptr()+m_rules.size(); }

        decl2rules::iterator begin_grouped_rules() const { return m_head2rules.begin(); }
        decl2rules::iterator end_grouped_rules() const { return m_head2rules.end(); }

    };

    inline std::ostream& operator<<(std::ostream& out, rule_set const& r) { r.display(out); return out; }
    
};

#endif /* DL_RULE_SET_H_ */

