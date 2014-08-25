/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    product_set.h

Abstract:

    Product set relation.
    A product set is a tuple of sets.
    The meaning of a product set is the set of
    elements in the cross-product.
    A product set relation is a set of product sets, 
    and the meaning of this relation is the union of
    all elements from the products. 
    It is to be used when computing over product sets is
    (much) cheaper than over the space of tuples.

Author:

    Nikolaj Bjorner (nbjorner) 2014-08-23

Revision History:

--*/
#ifndef _DL_PRODUCT_SET__H_
#define _DL_PRODUCT_SET__H_

#include "util.h"
#include "bit_vector.h"
#include "dl_base.h"
#include "dl_vector_relation.h"

namespace datalog {

    class product_set_plugin;

    class product_set : public vector_relation<bit_vector> {
        typedef bit_vector T;
        unsigned m_refs;
    public:
        product_set(product_set_plugin& p, relation_signature const& s, bool is_empty, T const& t = T());
       
        virtual ~product_set() {}
        unsigned get_hash() const;
        bool operator==(product_set const& p) const;
        bool contains(product_set const& p) const;

        void inc_ref() { ++m_refs; }
        void dec_ref() { --m_refs; if (0 == m_refs) dealloc(this); }
        unsigned ref_count() const { return m_refs; }

        struct eq {
            bool operator()(product_set const* s1, product_set const* s2) const {
                return *s1 == *s2;
            }
        };

        struct hash {
            unsigned operator()(product_set const* s) const {
                return s->get_hash();
            }
        };

        virtual void add_fact(const relation_fact & f);
        virtual bool contains_fact(const relation_fact & f) const;
        virtual relation_base * clone() const;
        virtual relation_base * complement(func_decl*) const;
        virtual void to_formula(expr_ref& fml) const;

        bool mk_intersect(unsigned idx, T const& t);

    private:
        virtual void display_index(unsigned i, const T&, std::ostream& out) const;
        virtual T mk_intersect(T const& t1, T const& t2, bool& _is_empty) const {
            T result(t1);
            result &= t2;
            _is_empty = is_empty(0, result);
            return result;
        }

        virtual T mk_widen(T const& t1, T const& t2) const {
            UNREACHABLE();
            return t1;
        }

        virtual T mk_unite(T const& t1, T const& t2) const {
            UNREACHABLE();
            return t1;
        }

        virtual bool is_subset_of(T const& t1, T const& t2) const {
            return t2.contains(t1);
        }

        virtual bool is_full(T const& t) const {
            for (unsigned j = 0; j < t.size(); ++j) {
                if (!t.get(j)) return false;
            }
            return true;
        }

        virtual bool is_empty(unsigned i, T const& t) const {
            for (unsigned j = 0; j < t.size(); ++j) {
                if (t.get(j)) return false;
            }
            return true;
        }

        virtual void mk_rename_elem(T& t, unsigned col_cnt, unsigned const* cycle) {
            // no-op.
        }

        virtual T mk_eq(union_find<> const& old_eqs, union_find<> const& neq_eqs, T const& t) const { 
            UNREACHABLE();
            return t; 
        }


    };

    typedef ptr_hashtable<product_set, product_set::hash, product_set::eq> product_sets;

    class product_set_relation : public relation_base {
        friend class product_set_plugin;
        product_sets m_elems;
    public:
        product_set_relation(product_set_plugin& p, relation_signature const& s);
        virtual ~product_set_relation();
        virtual void add_fact(const relation_fact & f);
        virtual bool contains_fact(const relation_fact & f) const;
        virtual product_set_relation * clone() const;
        virtual product_set_relation * complement(func_decl*) const;
        virtual void to_formula(expr_ref& fml) const;
        product_set_plugin& get_plugin() const; 
        virtual bool empty() const { return m_elems.empty(); }
        virtual void display(std::ostream& out) const;

        virtual bool is_precise() const { return true; }
    };

    class product_set_plugin : public relation_plugin {
        friend class product_set_relation;
        class join_fn;
        class project_fn;
        class union_fn;
        class rename_fn;
        class filter_equal_fn;
        class filter_identical_fn;
        class filter_interpreted_fn;
        class filter_by_negation_fn;        

    public:        
        product_set_plugin(relation_manager& rm);
        virtual bool can_handle_signature(const relation_signature & s);
        static symbol get_name() { return symbol("product_set"); }
        virtual relation_base * mk_empty(const relation_signature & s);
        virtual relation_base * mk_full(func_decl* p, const relation_signature & s);
        virtual relation_join_fn * mk_join_fn(const relation_base & t1, const relation_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2);
        virtual relation_transformer_fn * mk_project_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * removed_cols);
        virtual relation_transformer_fn * mk_rename_fn(const relation_base & t, unsigned permutation_cycle_len, 
            const unsigned * permutation_cycle);
        virtual relation_union_fn * mk_union_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta);
        virtual relation_union_fn * mk_widen_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta);
        virtual relation_mutator_fn * mk_filter_identical_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * identical_cols);
        virtual relation_mutator_fn * mk_filter_equal_fn(const relation_base & t, const relation_element & value, 
            unsigned col);
        virtual relation_mutator_fn * mk_filter_interpreted_fn(const relation_base & t, app * condition);

        unsigned set_size(sort* ty);

    private:
        static product_set_relation& get(relation_base& r);
        static product_set_relation* get(relation_base* r);
        static product_set_relation const & get(relation_base const& r);   
        product_set* insert(product_set* s, product_set_relation* r);
    };

};

#endif