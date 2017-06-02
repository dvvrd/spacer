/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_rule_dependencies.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-17.


Revision History:

    Generic implementation 2017-06-02 (dvvrd)


--*/
#ifndef DL_RULE_DEPENDENCIES_H_
#define DL_RULE_DEPENDENCIES_H_

#include<algorithm>
#include<functional>
#include"dl_rule_set.h"
#include"dl_context.h"
#include"ast_pp.h"

namespace datalog {

    class rule_set;

    template<typename T>
    class rule_dependencies_base {
    public:
        typedef obj_hashtable<T> item_set;
        typedef obj_map<T, item_set * > deps_type;

        typedef typename deps_type::iterator iterator;
    protected:
        /**
           Map (dependent -> set of master objects)

           Each master object is also present as a key of the map, even if its master set
           is empty.
        */
        deps_type        m_data;
        context &        m_context;
        ptr_vector<expr> m_todo;
        expr_sparse_mark m_visited;


        //we need to take care with removing to avoid memory leaks
        void remove_m_data_entry(T * key) {
            item_set * itm_set = m_data.find(key);
            dealloc(itm_set);
            m_data.remove(key);
        }

        //sometimes we need to return reference to an empty set,
        //so we return reference to this one.
        item_set m_empty_item_set;

        item_set & ensure_key(T * pred) {
            typename deps_type::obj_map_entry * e = m_data.insert_if_not_there2(pred, 0);
            if (!e->get_data().m_value) {
                e->get_data().m_value = alloc(item_set);
            }
            return *e->get_data().m_value;
        }

        void insert(T * depending, T * master) {
            SASSERT(m_data.contains(master)); //see m_data documentation
            item_set & s = ensure_key(depending);
            s.insert(master);
        }

        virtual void populate_one(rule * r) {}

    public:
        rule_dependencies_base(context& ctx): m_context(ctx) {}
        rule_dependencies_base(const rule_dependencies_base & o, bool reversed = false):
            m_context(o.m_context) {
            if (reversed) {
                iterator oit = o.begin();
                iterator oend = o.end();
                for (; oit!=oend; ++oit) {
                    T * pred = oit->m_key;
                    item_set & orig_items = *oit->get_value();

                    ensure_key(pred);
                    typename item_set::iterator dit = orig_items.begin();
                    typename item_set::iterator dend = orig_items.end();
                    for (; dit!=dend; ++dit) {
                        T * master_pred = *dit;
                        insert(master_pred, pred);
                    }
                }
            }
            else {
                iterator oit = o.begin();
                iterator oend = o.end();
                for (; oit!=oend; ++oit) {
                    T * pred = oit->m_key;
                    item_set & orig_items = *oit->get_value();
                    m_data.insert(pred, alloc(item_set, orig_items));
                }
            }
        }

        ~rule_dependencies_base() {
            reset();
        }

        void reset() {
            reset_dealloc_values(m_data);
        }

        void populate(const rule_set & rules) {
            SASSERT(m_data.empty());
            rule_set::decl2rules::iterator it  = rules.begin_grouped_rules();
            rule_set::decl2rules::iterator end = rules.end_grouped_rules();
            for (; it != end; ++it) {
                ptr_vector<rule> * rules = it->m_value;
                typename ptr_vector<rule>::iterator it2  = rules->begin();
                typename ptr_vector<rule>::iterator end2 = rules->end();
                for (; it2 != end2; ++it2) {
                    populate_one(*it2);
                }
            }
        }
        void populate(unsigned n, rule * const * rules) {
            SASSERT(m_data.empty());
            for (unsigned i=0; i<n; i++) {
                populate_one(rules[i]);
            }
        }

        void restrict(const item_set & allowed) {
            ptr_vector<T> to_remove;
            iterator pit = begin();
            iterator pend = end();
            for (; pit!=pend; ++pit) {
                T * pred = pit->m_key;
                if (!allowed.contains(pred)) {
                    to_remove.insert(pred);
                    continue;
                }
                item_set& itms = *pit->get_value();
                set_intersection(itms, allowed);
            }
            typename ptr_vector<T>::iterator rit = to_remove.begin();
            typename ptr_vector<T>::iterator rend = to_remove.end();
            for (; rit != rend; ++rit) {
                remove_m_data_entry(*rit);
            }
        }


        void remove(T * itm) {
            remove_m_data_entry(itm);
            iterator pit = begin();
            iterator pend = end();
            for (; pit != pend; ++pit) {
                item_set & itms = *pit->get_value();
                itms.remove(itm);
            }
        }
        void remove(const item_set & to_remove) {
            typename item_set::iterator rit = to_remove.begin();
            typename item_set::iterator rend = to_remove.end();
            for (; rit!=rend; ++rit) {
                remove_m_data_entry(*rit);
            }
            iterator pit = begin();
            iterator pend = end();
            for (; pit!=pend; ++pit) {
                item_set * itms = pit->get_value();
                set_difference(*itms, to_remove);
            }
        }


        bool empty() const { return m_data.empty(); }
        const item_set & get_deps(T * f) const {
            typename deps_type::obj_map_entry * e = m_data.find_core(f);
            if (!e) {
                return m_empty_item_set;
            }
            SASSERT(e->get_data().get_value());
            return *e->get_data().get_value();
        }

        /**
           \brief Number of predicates \c f depends on.
         */
        unsigned in_degree(T * f) const { return get_deps(f).size(); }
        /**
           \brief Number of predicates that depend on \c f.
         */
        unsigned out_degree(T * f) const {
            unsigned res = 0;
            iterator pit = begin();
            iterator pend = end();
            for (; pit!=pend; ++pit) {
                item_set & itms = *pit->get_value();
                if (itms.contains(f)) {
                    res++;
                }
            }
            return res;
        }

        
        /**
           \brief If the rependency graph is acyclic, put all elements into \c res
             ordered so that elements can depend only on elements that are before them.
             If the graph is not acyclic, return false.
         */
        bool sort_deps(ptr_vector<T> & res) {
            typedef obj_map<T, unsigned> deg_map;
            unsigned init_len = res.size();
            deg_map degs;
            unsigned curr_index = init_len;
            rule_dependencies_base<T> reversed(*this, true);

            iterator pit = begin();
            iterator pend = end();
            for (; pit!=pend; ++pit) {
                T * pred = pit->m_key;
                unsigned deg = in_degree(pred);
                if (deg==0) {
                    res.push_back(pred);
                }
                else {
                    degs.insert(pred, deg);
                }
            }

            while (curr_index<res.size()) { //res.size() can change in the loop iteration
                T * curr = res[curr_index];
                const item_set & children = reversed.get_deps(curr);
                typename item_set::iterator cit = children.begin();
                typename item_set::iterator cend = children.end();
                for (; cit!=cend; ++cit) {
                    T * child = *cit;
                    typename deg_map::obj_map_entry * e = degs.find_core(child);
                    SASSERT(e);
                    unsigned & child_deg = e->get_data().m_value;
                    SASSERT(child_deg>0);
                    child_deg--;
                    if (child_deg==0) {
                        res.push_back(child);
                    }
                }
                curr_index++;
            }
            if (res.size() < init_len + m_data.size()) {
                res.shrink(init_len);
                return false;
            }
            SASSERT(res.size()==init_len+m_data.size());
            return true;
        }


        iterator begin() const { return m_data.begin(); }
        iterator end() const { return m_data.end(); }
    };

    template<typename T>
    class rule_stratifier_base {
    public:
        typedef obj_hashtable<T> item_set;
        typedef ptr_vector<item_set> comp_vector;
        typedef obj_map<T, item_set *> deps_type;
    protected:

        const rule_dependencies_base<T> & m_deps;
        comp_vector m_strats;

        obj_map<T, unsigned> m_preorder_nums;
        ptr_vector<T> m_stack_S;
        ptr_vector<T> m_stack_P;

        obj_map<T, unsigned> m_component_nums;
        comp_vector m_components;
        obj_map<T, unsigned> m_pred_strat_nums;

        unsigned m_next_preorder;
        unsigned m_first_preorder;

        /**
            Finds strongly connected components using the Gabow's algorithm.
        */
        void traverse(T* el) {
            unsigned p_num;
            if (m_preorder_nums.find(el, p_num)) {
                if (p_num < m_first_preorder) {
                    //traversed in a previous sweep
                    return;
                }
                if (m_component_nums.contains(el)) {
                    //we already assigned a component for el
                    return;
                }
                while (!m_stack_P.empty()) {
                    unsigned on_stack_num;
                    VERIFY( m_preorder_nums.find(m_stack_P.back(), on_stack_num) );
                    if (on_stack_num <= p_num) {
                        break;
                    }
                    m_stack_P.pop_back();
                }
            }
            else {
                p_num=m_next_preorder++;
                m_preorder_nums.insert(el, p_num);

                m_stack_S.push_back(el);
                m_stack_P.push_back(el);

                const item_set & children = m_deps.get_deps(el);
                typename item_set::iterator cit=children.begin();
                typename item_set::iterator cend=children.end();
                for (; cit!=cend; ++cit) {
                    traverse(*cit);
                }

                if (el == m_stack_P.back()) {
                    unsigned comp_num = m_components.size();
                    item_set * new_comp = alloc(item_set);
                    m_components.push_back(new_comp);

                    T* s_el;
                    do {
                        s_el=m_stack_S.back();
                        m_stack_S.pop_back();
                        new_comp->insert(s_el);
                        m_component_nums.insert(s_el, comp_num);
                    } while (s_el!=el);
                    m_stack_P.pop_back();
                }
            }
        }


        /**
            Calls \c traverse to identify strognly connected components and then
            orders them using topological sorting.
        */
        void process() {
            if (m_deps.empty()) {
                return;
            }

            //detect strong components
            typename rule_dependencies_base<T>::iterator it = m_deps.begin();
            typename rule_dependencies_base<T>::iterator end = m_deps.end();
            for (; it!=end; ++it) {
                T * el = it->m_key;
                //we take a note of the preorder number with which this sweep started
                m_first_preorder = m_next_preorder;
                traverse(el);
            }

            //do topological sorting

            //degres of components (number of inter-component edges ending up in the component)
            svector<unsigned> in_degrees;
            in_degrees.resize(m_components.size());

            //init in_degrees
            it = m_deps.begin();
            end = m_deps.end();
            for (; it != end; ++it) {
                T * el = it->m_key;
                item_set * out_edges = it->m_value;

                unsigned el_comp;
                VERIFY( m_component_nums.find(el, el_comp) );

                typename item_set::iterator eit = out_edges->begin();
                typename item_set::iterator eend = out_edges->end();
                for (; eit!=eend; ++eit) {
                    T * tgt = *eit;

                    unsigned tgt_comp = m_component_nums.find(tgt);

                    if (el_comp != tgt_comp) {
                        in_degrees[tgt_comp]++;
                    }
                }
            }


            // We put components whose indegree is zero to m_strats and assign its 
            // m_components entry to zero.
            unsigned comp_cnt = m_components.size();
            for (unsigned i = 0; i < comp_cnt; i++) {
                if (in_degrees[i] == 0) {
                    m_strats.push_back(m_components[i]);
                    m_components[i] = 0;
                }
            }

            SASSERT(!m_strats.empty()); //the component graph is acyclic and non-empty

            //we remove edges from components with zero indegre building the topological ordering
            unsigned strats_index = 0;
            while (strats_index < m_strats.size()) { //m_strats.size() changes inside the loop!
                item_set * comp = m_strats[strats_index];
                typename item_set::iterator cit=comp->begin();
                typename item_set::iterator cend=comp->end();
                for (; cit!=cend; ++cit) {
                    T * el = *cit;
                    const item_set & deps = m_deps.get_deps(el);
                    typename item_set::iterator eit=deps.begin();
                    typename item_set::iterator eend=deps.end();
                    for (; eit!=eend; ++eit) {
                        T * tgt = *eit;
                        unsigned tgt_comp;
                        VERIFY( m_component_nums.find(tgt, tgt_comp) );

                        //m_components[tgt_comp]==0 means the edge is intra-component.
                        //Otherwise it would go to another component, but it is not possible, since
                        //as m_components[tgt_comp]==0, its indegree has already reached zero.
                        if (m_components[tgt_comp]) {
                            SASSERT(in_degrees[tgt_comp]>0);
                            in_degrees[tgt_comp]--;
                            if (in_degrees[tgt_comp]==0) {
                                m_strats.push_back(m_components[tgt_comp]);
                                m_components[tgt_comp] = 0;
                            }
                        }
                        traverse(*cit);
                    }
                }
                strats_index++;
            }
            //we have managed to topologicaly order all the components
            SASSERT(std::find_if(m_components.begin(), m_components.end(), 
                std::bind1st(std::not_equal_to<item_set*>(), (item_set*)0)) == m_components.end());

            //reverse the strats array, so that the only the later components would depend on earlier ones
            std::reverse(m_strats.begin(), m_strats.end());

            SASSERT(m_pred_strat_nums.empty());
            unsigned strat_cnt = m_strats.size();
            for (unsigned strat_index=0; strat_index<strat_cnt; strat_index++) {
                item_set * comp = m_strats[strat_index];
                typename item_set::iterator cit=comp->begin();
                typename item_set::iterator cend=comp->end();
                for (; cit != cend; ++cit) {
                    T * el = *cit;
                    m_pred_strat_nums.insert(el, strat_index);
                }
            }

            //finalize structures that are not needed anymore
            m_preorder_nums.finalize();
            m_stack_S.finalize();
            m_stack_P.finalize();
            m_component_nums.finalize();
            m_components.finalize();
        }

    public:

        /**
            \remark The \c stratifier object keeps a reference to the \c deps object, so
            it must exist for the whole lifetime of the \c stratifier object.
        */
        rule_stratifier_base(const rule_dependencies_base<T> & deps)
            : m_deps(deps), m_next_preorder(0) 
        {
            process();
        }

        ~rule_stratifier_base() {
            typename comp_vector::iterator it = m_strats.begin();
            typename comp_vector::iterator end = m_strats.end();
            for (; it!=end; ++it) {
                SASSERT(*it);
                dealloc(*it);
            }
        }

        /**
            Return vector of components ordered so that the only dependencies are from
            later components to earlier.
        */
        const comp_vector & get_strats() const { return m_strats; }

        unsigned get_strat(T * pred) const {
            unsigned num;
            if (!m_pred_strat_nums.find(pred, num)) {
                //the number of the predicate is not stored, therefore it did not appear 
                //in the algorithm and therefore it does not depend on anything and nothing 
                //depends on it. So it is safe to assign zero strate to it, although it is
                //not strictly true.
                num = 0;
            }
            return num;
        }
    };

    class rule_dependencies : public rule_dependencies_base<func_decl> {
    private:
        virtual void populate_one(rule * r) {
            TRACE("dl_verbose", tout << r->get_decl()->get_name() << "\n";);
            m_visited.reset();
            func_decl * d = r->get_decl();
            func_decl_set & s = ensure_key(d);

            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                m_todo.push_back(r->get_tail(i));
            }
            while (!m_todo.empty()) {
                expr* e = m_todo.back();
                m_todo.pop_back();
                if (m_visited.is_marked(e)) {
                    continue;
                }
                m_visited.mark(e, true);
                if (is_app(e)) {
                    app* a = to_app(e);
                    d = a->get_decl();
                    if (m_context.is_predicate(d)) {
                        // insert d and ensure the invariant 
                        // that every predicate is present as 
                        // a key in m_data
                        s.insert(d);
                        ensure_key(d);
                    }
                    m_todo.append(a->get_num_args(), a->get_args());
                }
                else if (is_quantifier(e)) {
                    m_todo.push_back(to_quantifier(e)->get_expr());
                }
            }
        }

    public:
        rule_dependencies(context& ctx) : rule_dependencies_base(ctx) {}
        rule_dependencies(const rule_dependencies_base & o, bool reversed = false)  : rule_dependencies_base(o, reversed) {}
        ~rule_dependencies() {}

        void display( std::ostream & out ) const {
            iterator pit = begin();
            iterator pend = end();
            for (; pit != pend; ++pit) {
                func_decl * pred = pit->m_key;
                const item_set & deps = *pit->m_value;
                item_set::iterator dit=deps.begin();
                item_set::iterator dend=deps.end();
                if (dit == dend) {
                    out<<pred->get_name()<<" - <none>\n";
                }
                for (; dit != dend; ++dit) {
                    func_decl * dep = *dit;
                    out << pred->get_name() << " -> " << dep->get_name() << "\n";
                }
            }
        }
    };

    class rule_stratifier : public rule_stratifier_base<func_decl> {
    private:
        const rule_dependencies & m_deps;
    public:
        rule_stratifier(const rule_dependencies & deps) : rule_stratifier_base(deps), m_deps(deps) {}
        ~rule_stratifier() {}

        void display( std::ostream & out ) const {
            m_deps.display(out << "dependencies\n");
            out << "strata\n";
            for (unsigned i = 0; i < m_strats.size(); ++i) {
                item_set::iterator it  = m_strats[i]->begin();
                item_set::iterator end = m_strats[i]->end();
                for (; it != end; ++it) {
                    out << (*it)->get_name() << " ";
                }
                out << "\n";
            }
        }
    };

};

#endif /* DL_RULE_DEPENDENCIES_H_ */
