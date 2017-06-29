/*++
Copyright (c) 2017 Saint-Petersburg State University

Module Name:

    dl_mk_synchronize.h

Abstract:

    Rule transformer that attempts to merge recursive iterations
    relaxing the shape of the inductive invariant.

Author:

    Dmitry Mordvinov (dvvrd) 2017-05-24

Revision History:

--*/
#include "dl_mk_synchronize.h"
#include "ast_util.h"
#include "expr_safe_replace.h"

namespace datalog {

    // -----------------------------------
    //
    // utils
    //
    // -----------------------------------

    struct scoped_push {
    private:
        smt::kernel & m_solver;
    public:
        scoped_push(smt::kernel & solver) : m_solver(solver) {
            m_solver.push();
        }
        ~scoped_push() {
            m_solver.pop(1);
        }
    };

    symbol concat(char const * s, unsigned n) {
        std::stringstream ss;
        ss << s << n;
        return symbol(ss.str().c_str());
    }

    vector<ptr_vector<expr> > replace_bound_vars(ast_manager & m, bool with_consts, unsigned & delta,
            vector<ptr_vector<expr> > const & exprs, ptr_vector<sort> & var_sorts, svector<symbol> & var_names) {
        used_vars used;
        for (vector<ptr_vector<expr> >::const_iterator it1 = exprs.begin(); it1 != exprs.end(); ++it1) {
            ptr_vector<expr> const & v = *it1;
            for (ptr_vector<expr>::const_iterator it2 = v.begin(); it2 != v.end(); ++it2) {
                used.process(*it2);
            }
        }

        ptr_vector<sort> sorts;
        unsigned sz = used.get_max_found_var_idx_plus_1();
        for (unsigned i = 0; i < sz; ++i) {
            sort* s = used.get(i);
            sorts.push_back(s ? s : m.mk_bool_sort());
        }

        expr_ref_vector revsub(m);
        revsub.resize(sorts.size());
        for (unsigned i = 0; i < sorts.size(); ++i) {
            expr * bv = with_consts ? static_cast<expr*>(m.mk_fresh_const("__cv", sorts[i])) : m.mk_var(delta, sorts[i]);
            revsub[i] = bv;
            var_sorts.push_back(sorts[i]);
            var_names.push_back(with_consts ? to_app(bv)->get_decl()->get_name() : concat("__bv", delta));
            ++delta;
        }

        expr_ref tmp(m);
        var_subst vs(m, false);
        vector<ptr_vector<expr> > result;
        result.resize(exprs.size());
        for (unsigned i = 0; i < exprs.size(); ++i) {
            ptr_vector<expr> const & v = exprs[i];
            result[i].resize(exprs[i].size());
            for (unsigned j = 0; j < exprs[i].size(); ++j) {
                vs(exprs[i][j], revsub.size(), revsub.c_ptr(), tmp);
                result[i][j] = tmp.steal();
            }
        }
        return result;
    }

    ptr_vector<expr> replace_vars_with_consts(ast_manager & m, unsigned & delta, unsigned num_exprs, expr * const* exprs) {
        vector<ptr_vector<expr> > input;
        ptr_vector<sort> tmp1;
        svector<symbol> tmp2;
        input.push_back(ptr_vector<expr>(num_exprs, exprs));
        return replace_bound_vars(m, true, delta, input, tmp1, tmp2)[0];
    }

    bool is_non_recursive_rule(rule & r) {
        func_decl * f = r.get_head()->get_decl();
        for (unsigned i = 0; i < r.get_uninterpreted_tail_size(); ++i) {
            if (r.get_tail(i)->get_decl() == f) {
                return false;
            }
        }
        return true;
    }

    // -----------------------------------
    //
    // rules reachability
    //
    // -----------------------------------

    rule_reachability_graph::rule_reachability_graph(context & ctx, rule_set const & rules)
          : rule_dependencies_base(ctx),
            m_rules(rules),
            m_unify(ctx) {
        populate(rules);
    }

    rule_reachability_graph::~rule_reachability_graph() {
    }

    bool rule_reachability_graph::check_reachability(rule & src, unsigned tail_idx, rule & dst, rule_ref & tmp) {
        // TODO: m_unify.apply simply simplifies interpreted tail. Here we should check it for satisfiability!
        return m_unify.unify_rules(src, tail_idx, dst) && m_unify.apply(src, tail_idx, dst, tmp);
        // if (m_unify.unify_rules(src, tail_idx, dst) &&
        //     m_unify.apply(src, tail_idx, dst, tmp)) {
        //     expr_ref_vector s1 = m_unify.get_rule_subst(src, true);
        //     expr_ref_vector s2 = m_unify.get_rule_subst(dst, false);
        //     resolve_rule(m_rules.get_rule_manager(), src, dst, tail_idx, s1, s2, *tmp.get());
        //     return true;
        // }

        // return false;
    }

    void rule_reachability_graph::populate_one(rule * r) {
        TRACE("dl_verbose", tout << r->get_decl()->get_name() << "\n";);
        m_visited.reset();
        item_set & s = ensure_key(r);
        s.insert(r);

        rule_ref tmp_rule(m_rules.get_rule_manager());
        for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
            const rule_vector &potential_deps = m_rules.get_predicate_rules(r->get_tail(i)->get_decl());
            rule_vector::const_iterator it = potential_deps.begin(), end = potential_deps.end();
            for (; it != end; ++it) {
                rule * dst = *it;
                if (!s.contains(dst) && check_reachability(*r, i, *dst, tmp_rule)) {
                    s.insert(dst);
                    ensure_key(dst);
                }
            }
        }
    }

    void rule_reachability_graph::connect(rule * r1, rule * r2) {
        item_set & s = ensure_key(r1);
        if (!s.contains(r2)) {
            s.insert(r2);
            ensure_key(r2);
        }
    }

    void rule_reachability_graph::display( std::ostream & out ) const {
        iterator pit = begin();
        iterator pend = end();
        for (; pit != pend; ++pit) {
            rule * r = pit->m_key;
            const item_set & deps = *pit->m_value;
            item_set::iterator dit = deps.begin();
            item_set::iterator dend = deps.end();
            if (dit == dend) {
                out << r->name() << " - <none>\n";
            }
            for (; dit != dend; ++dit) {
                rule * dep = *dit;
                out << r->name() << " -> " << dep->name() << "\n";
            }
        }
    }

    reachability_stratifier::reachability_stratifier(rule_reachability_graph const & graph)
          : rule_stratifier_base(graph),
            m_graph(graph) {
    }

    reachability_stratifier::~reachability_stratifier() {
    }

    bool reachability_stratifier::validate_mutual_recursion() const {
        for (unsigned i = 0; i < m_strats.size(); ++i) {
            item_set::iterator it  = m_strats[i]->begin();
            item_set::iterator end = m_strats[i]->end();
            func_decl * head;
            if (it != end) {
                head = (*it)->get_head()->get_decl();
            }
            for (; it != end; ++it) {
                if ((*it)->get_head()->get_decl() != head) {
                    IF_VERBOSE (1, verbose_stream () << "Synchronization of mutual recursion is currently not supported";);
                    return false;
                }
            }
        }
        return true;
    }

    void reachability_stratifier::display( std::ostream & out ) const {
        m_graph.display(out << "dependencies\n");
        out << "strata\n";
        for (unsigned i = 0; i < m_strats.size(); ++i) {
            item_set::iterator it  = m_strats[i]->begin();
            item_set::iterator end = m_strats[i]->end();
            for (; it != end; ++it) {
                out << (*it)->name() << " ";
            }
            out << "\n";
        }
    }

    bool reachability_stratifier::strata_connected(item_set & src, item_set & dst) const {
        for (item_set::iterator it1 = src.begin(); it1 != src.end(); ++it1) {
            for (item_set::iterator it2 = dst.begin(); it2 != dst.end(); ++it2) {
                if (m_graph.get_deps(*it1).contains(*it2)) {
                    return true;
                }
            }
        }
        return false;
    }

    bool reachability_stratifier::is_non_recursive_stratum(item_set & s) const {
        return s.size() == 1 && is_non_recursive_rule(**s.begin());
    }

    // -----------------------------------
    //
    // synchronization lemma
    //
    // -----------------------------------

    lemma::lemma(ast_manager & m, ptr_vector<expr> const & constraint, ptr_vector<expr> const & holes)
          : m(m),
            m_constraint(constraint),
            m_holes(holes),
            m_hole_enabled(m_holes.size(), true)
    {}

    lemma::lemma(ast_manager & m, ptr_vector<lemma> const & combined_lemmas)
          : m(m) {
        // For now we consider that combined lemmas have one common source and just generalize its constraint.
        // Under such conditions resulting lemma is just an intersection of constraints.
        if (combined_lemmas.empty()) {
            return;
        }
        m_holes = combined_lemmas[0]->m_holes;
        m_hole_enabled = svector<bool>(m_holes.size(), true);
        ptr_vector<lemma>::const_iterator it = combined_lemmas.begin(), end = combined_lemmas.end();
        lemma * first_lemma = *it;
        ++it;
        for (unsigned i = 0; i < first_lemma->m_constraint.size(); ++i) {
            expr * candidate_constraint = first_lemma->m_constraint[i];
            bool in_every_lemma = true;
            for (; it != end; ++it) {
                if (!(*it)->m_constraint.contains(candidate_constraint)) {
                    in_every_lemma = false;
                    break;
                }
            }
            if (in_every_lemma) {
                m_constraint.push_back(candidate_constraint);
            }
        }
        for (unsigned i = 0; i < first_lemma->m_hole_enabled.size(); ++i) {
            bool in_every_lemma = true;
            for (; it != end; ++it) {
                if (!(*it)->m_hole_enabled[i]) {
                    in_every_lemma = false;
                    break;
                }
            }
            m_hole_enabled[i] = in_every_lemma;
        }
    }

    lemma::lemma(ast_manager & m, lemma & source, ptr_vector<expr> const & old_assumption_vars, obj_hashtable<expr> const & new_assumption_vars)
          : m(m),
            m_holes(source.m_holes),
            m_hole_enabled(source.m_hole_enabled) {
        for (unsigned i = 0; i < source.m_constraint.size(); ++i) {
            if (new_assumption_vars.contains(old_assumption_vars[i])) {
                m_constraint.push_back(source.m_constraint[i]);
            }
        }
        for (unsigned i = 0, j = source.m_constraint.size(); i < source.m_holes.size(); ++i) {
            if (m_hole_enabled[i] && !new_assumption_vars.contains(old_assumption_vars[j++])) {
                m_hole_enabled[i] = false;
            }
        }
    }

    void lemma::fill_holes(bool replace_with_consts, unsigned num_exprs, expr * const* exprs, unsigned & delta, ptr_vector<expr> & result,
            ptr_vector<sort> & var_sorts, svector<symbol> & var_names) {
        SASSERT(num_exprs == m_holes.size());
        ptr_vector<expr> new_holes;
        replace_bound_vars_in_this(replace_with_consts, delta, result, new_holes, var_sorts, var_names);
        for (unsigned i = 0; i < new_holes.size(); ++i) {
            if (m_hole_enabled[i]) {
                result.push_back(m.mk_eq(exprs[i], new_holes[i]));
            }
        }
    }

    void lemma::replace_bound_vars_in_this(bool with_consts, unsigned & delta, ptr_vector<expr> & new_constraint, ptr_vector<expr> & new_holes,
            ptr_vector<sort> & var_sorts, svector<symbol> & var_names) {
        vector<ptr_vector<expr> > input;
        input.push_back(m_constraint);
        input.push_back(m_holes);
        vector< ptr_vector<expr> > output = replace_bound_vars(m, with_consts, delta, input, var_sorts, var_names);
        SASSERT(output.size() == 2);
        new_constraint = output[0];
        new_holes = output[1];
    }

    expr_ref_vector lemma::operator()(obj_hashtable<rule> const & rs, ptr_vector<expr> & assumption_vars, ptr_vector<expr> & conclusions,
            ptr_vector<sort> & free_var_sorts, svector<symbol> & free_var_names) {
        unsigned n = m_constraint.size();
        unsigned delta = 0;
        expr_ref_vector result(m);
        vector<ptr_vector<expr> > head_implicants;
        vector<ptr_vector<expr> > call_implicants;
        assumption_vars.reset(); assumption_vars.resize(n);
        conclusions.reset();
        for (unsigned i = 0; i < n; ++i) {
            expr * premise_var = m.mk_fresh_const("__pr", m.mk_bool_sort());
            assumption_vars[i] = premise_var;
        }
        for (unsigned i = 0, j = n; i < m_holes.size(); ++i) {
            if (m_hole_enabled[i]) {
                expr * premise_var = m.mk_fresh_const("__pr", m.mk_bool_sort());
                assumption_vars.push_back(premise_var);
            }
        }

        for (obj_hashtable<rule>::iterator it = rs.begin(); it != rs.end(); ++it) {
            rule & r = **it;

            vector< ptr_vector<expr> > to_rename;
            ptr_vector<expr> interpreted_tail;
            for (unsigned i = r.get_uninterpreted_tail_size(); i < r.get_tail_size(); ++i) {
                interpreted_tail.push_back(r.get_tail(i));
            }
            to_rename.push_back(interpreted_tail);
            to_rename.push_back(ptr_vector<expr>(r.get_head()->get_num_args(), r.get_head()->get_args()));
            for (unsigned i = 0; i < r.get_uninterpreted_tail_size(); ++i) {
                app * app = r.get_tail(i);
                if (app->get_decl() == r.get_head()->get_decl()) {
                    to_rename.push_back(ptr_vector<expr>(app->get_num_args(), app->get_args()));
                }
            }

            // TODO: make everything expr_ref_list!
            vector< ptr_vector<expr> > renamed_exprs = replace_bound_vars(m, true, delta, to_rename, free_var_sorts, free_var_names);
            for (unsigned i = 0; i < renamed_exprs[0].size(); ++i) {
                result.push_back(renamed_exprs[0][i]);
            }

            ptr_vector<expr> tmp;
            fill_holes(true, renamed_exprs[1].size(), renamed_exprs[1].c_ptr(), delta, tmp, free_var_sorts, free_var_names);
            head_implicants.push_back(tmp);
            free_var_sorts.reset();
            free_var_names.reset();
            delta = 0;
            for (unsigned i = 2; i < renamed_exprs.size(); ++i) {
                tmp.reset();
                fill_holes(false, renamed_exprs[i].size(), renamed_exprs[i].c_ptr(), delta, tmp, free_var_sorts, free_var_names);
                call_implicants.push_back(tmp);
            }
        }

        for (unsigned i = 0; i < assumption_vars.size(); ++i) {
            ptr_vector<expr> implied_heads;
            ptr_vector<expr> implied_calls;
            implied_heads.resize(head_implicants.size());
            implied_calls.resize(call_implicants.size());
            for (unsigned j = 0; j < implied_heads.size(); ++j) {
                implied_heads[j] = head_implicants[j][i];
            }
            for (unsigned j = 0; j < implied_calls.size(); ++j) {
                implied_calls[j] = call_implicants[j][i];
            }
            expr * head_conj = m.mk_and(implied_heads.size(), implied_heads.c_ptr());
            expr * call_conj = m.mk_and(implied_calls.size(), implied_calls.c_ptr());
            result.push_back(m.mk_implies(assumption_vars[i], head_conj));
            conclusions.push_back(call_conj);
        }

        flatten_and(result);
        return result;
    }

    unsigned lemma::weight() const {
        unsigned result = m_constraint.size();
        for (unsigned i = 0; i < m_hole_enabled.size(); ++i) {
            if (m_hole_enabled[i]) ++result;
        }
        return result;
    }

    void lemma::display(std::ostream & out) {
        out << "constraint:";
        for (unsigned i = 0; i < m_constraint.size(); ++i) {
            out << " " << mk_pp(m_constraint[i], m);
        }
        out << "\n     holes:";
        for (unsigned i = 0; i < m_holes.size(); ++i) {
            out << " " << (m_hole_enabled[i] ? "" : "!!!") << mk_pp(m_holes[i], m);
        }
        out << "\n";
    }

    rule_ref lemma::enrich_rule(rule & r, rule_set & rules) {
        ptr_vector<sort> sorts;
        r.get_vars(m, sorts);
        ptr_vector<app> new_tail;
        svector<bool> new_tail_neg;
        new_tail.resize(r.get_tail_size());
        new_tail_neg.resize(r.get_tail_size());
        for (unsigned i = 0; i < r.get_tail_size(); ++i) {
            new_tail[i] = r.get_tail(i);
            new_tail_neg[i] = r.is_neg_tail(i);
        }
        unsigned delta = sorts.size();
        ptr_vector<expr> appendix;
        ptr_vector<sort> tmp1;
        svector<symbol> tmp2;
        fill_holes(false, r.get_head()->get_num_args(), r.get_head()->get_args(), delta, appendix, tmp1, tmp2);
        for (ptr_vector<expr>::const_iterator it = appendix.begin(); it != appendix.end(); ++it) {
            new_tail.push_back(to_app(*it));
            new_tail_neg.push_back(false);
        }

        rule_manager & rm = rules.get_rule_manager();
        rule_ref new_rule(rm);
        new_rule = rm.mk(r.get_head(), new_tail.size(), new_tail.c_ptr(), new_tail_neg.c_ptr(), r.name(), false);
        rules.replace_rule(&r, new_rule.get());
        return new_rule;
    }

    // -----------------------------------
    //
    // transformation
    //
    // -----------------------------------

    mk_synchronize::mk_synchronize(context& ctx, unsigned priority):
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_solver(m, m_smt_params)
    {}

    bool mk_synchronize::is_recursive_app(rule & r, app * app) const {
        return app && r.get_head() && r.get_head()->get_decl() == app->get_decl();
    }

    rule * mk_synchronize::get_original_rule(rule * r) {
        return m_rule2orig.count(r) ? m_rule2orig[r] : r;
    }

    rule_ref mk_synchronize::replace_applications(rule & r, ptr_vector<app> const & apps, func_decl * pred, app *& resulting_app) {
        resulting_app = product_application(apps, pred);

        ptr_vector<app> new_tail;
        svector<bool> new_tail_neg;
        unsigned n = r.get_tail_size() - apps.size() + 1;
        unsigned tail_idx = 0;
        new_tail.resize(n);
        new_tail_neg.resize(n);
        new_tail[0] = resulting_app;
        new_tail_neg[0] = false;

        // TODO: unify with product_application
        for (unsigned i = 0; i < r.get_positive_tail_size(); ++i) {
            app* tail = r.get_tail(i);
            if (!apps.contains(tail)) {
                ++tail_idx;
                new_tail[tail_idx] = tail;
                new_tail_neg[tail_idx] = false;
            }
        }
        for (unsigned i = r.get_positive_tail_size(); i < r.get_uninterpreted_tail_size(); ++i) {
            ++tail_idx;
            new_tail[tail_idx] = r.get_tail(i);
            new_tail_neg[tail_idx] = true;
        }
        for (unsigned i = r.get_uninterpreted_tail_size(); i < r.get_tail_size(); ++i) {
            ++tail_idx;
            new_tail[tail_idx] = r.get_tail(i);
            new_tail_neg[tail_idx] = false;
        }

        rule_ref new_rule(rm);
        new_rule = rm.mk(r.get_head(), tail_idx + 1,
            new_tail.c_ptr(), new_tail_neg.c_ptr(), /*symbol("REPLACED APPLICATION")*/r.name(), false);
        // m_rule2orig.insert(new_rule.get(), &r);
        m_rule2orig.insert(std::pair<rule*, rule*>(new_rule.get(), &r));
        return new_rule;
    }

    rule * mk_synchronize::rename_bound_vars_in_rule(rule * r, unsigned & var_idx) {
        ptr_vector<sort> sorts;
        r->get_vars(m, sorts);
        expr_ref_vector revsub(m);
        revsub.resize(sorts.size());
        for (unsigned i = 0; i < sorts.size(); ++i) {
            if (sorts[i]) {
                revsub[i] = m.mk_var(var_idx++, sorts[i]);
            }
        }

        rule_ref new_rule(rm);
        new_rule = rm.mk(r, r->name());
        rm.substitute(new_rule, revsub.size(), revsub.c_ptr());

        rule * result = new_rule.steal();
        m_rule2orig.insert(std::pair<rule*, rule*>(result, r));
        return result;
    }

    vector<rule_vector> mk_synchronize::rename_bound_vars(ptr_vector<func_decl> const & heads, rule_set & rules) {
        vector<rule_vector> result;
        result.resize(heads.size());
        unsigned var_idx = 0;
        for (unsigned i = 0; i < heads.size(); ++i) {
            func_decl * head = heads[i];
            rule_vector const & src_rules = rules.get_predicate_rules(head);
            rule_vector dst_vector;
            dst_vector.resize(src_rules.size());
            for (unsigned j = 0; j < src_rules.size(); ++j) {
                rule * new_rule = rename_bound_vars_in_rule(src_rules[j], var_idx);
                dst_vector[j] = new_rule;
            }
            result[i] = dst_vector;
        }
        return result;
    }

    lemma * mk_synchronize::mine_lemma_from_rule(rule & r, app * non_rec_app) const {
        ptr_vector<expr> conjuncts;
        ptr_vector<expr> holes;
        conjuncts.resize(r.get_tail_size() - r.get_uninterpreted_tail_size());
        for (unsigned i = r.get_uninterpreted_tail_size(), j = 0; i < r.get_tail_size(); ++i, ++j) {
            conjuncts[j] = r.get_tail(i);
        }
        return alloc(lemma, m, conjuncts, ptr_vector<expr>(non_rec_app->get_num_args(), non_rec_app->get_args()));
    }

    obj_hashtable<expr> mk_synchronize::extract_invariant(expr_ref_vector const & constraint, ptr_vector<expr> const & assumption_vars,
            ptr_vector<expr> const & conclusions, ptr_vector<sort> const & free_var_sorts, svector<symbol> const & free_var_names) {
        SASSERT(assumption_vars.size() == conclusions.size());
        unsigned n = assumption_vars.size();
        svector<bool> enabled(n, true);
        m_solver.reset();
        for (expr_ref_vector::iterator it = constraint.begin(); it != constraint.end(); ++it) {
            m_solver.assert_expr(*it);
            // std::cout << "1. asserting " << mk_pp(*it, m) << std::endl;
        }
        expr_ref_vector tmp_conclusions(m);
        for (expr_ref_vector::iterator it = conclusions.begin(); it != conclusions.end(); ++it) {
            tmp_conclusions.push_back(*it);
        } // TODO: expr_ref_vector should be passed initially!
        // unsigned counter = 0;
        bool success = false;
        while (true) {
            scoped_push push(m_solver);
            // ptr_vector<expr> conclusion_disjuncts;
            expr_ref_vector conclusion_disjuncts(m);
            for (unsigned i = 0; i < n; ++i) {
                if (enabled[i]) {
                    m_solver.assert_expr(assumption_vars[i]);
                    conclusion_disjuncts.push_back(m.mk_not(tmp_conclusions[i].get()));
                    // std::cout << "2. asserting " << mk_pp(assumption_vars[i], m) << std::endl;
                }
            }

            expr * conclusion_body = m.mk_or(conclusion_disjuncts.size(), conclusion_disjuncts.c_ptr());
            expr * conclusion = m.mk_forall(free_var_names.size(), free_var_sorts.c_ptr(), free_var_names.c_ptr(), conclusion_body);
            m_solver.assert_expr(conclusion);
            // std::cout << "3. asserting " << mk_pp(conclusion, m) << std::endl;
            // std::cout << "checking...\n";
            lbool is_sat = m_solver.check();
            // std::cout << "got " << is_sat << std::endl;
            if (is_sat == l_true) {
                model_ref model;
                m_solver.get_model(model);
                //----
                // expr_ref modelr(m);
                // model2expr(model, modelr);
                // std::cout << "model: " << mk_pp(modelr, m) << std::endl;
                //----
                // expr_ref valuation(m);
                // bool at_least_one_changed = false;
                // for (unsigned i = 0; i < n; ++i) {
                //     if (enabled[i]) {
                //         std::cout << "ASKING FOR " << mk_pp(conclusions[i], m) << std::endl;
                //         if (model->eval(conclusions[i], valuation) && m.is_false(valuation)) {
                //             std::cout << "DISABLING " << mk_pp(assumption_vars[i], m) << " and " << mk_pp(conclusions[i], m) << std::endl;
                //             enabled[i] = false;
                //             at_least_one_changed = true;
                //         }
                //         std::cout << "VALUATION IS " << mk_pp(valuation, m) << std::endl;
                //     }
                // }
                disable_minimal_unsatisfiable_subset(tmp_conclusions, model, enabled);
                // for (unsigned i = 0; i < conclusions.size(); ++i) {
                    // at_least_one_changed |= in_mus[i];
                    // if (!enabled[i]) {
                    //     std::cout << "DISABLING " << mk_pp(assumption_vars[i], m) << " and " << mk_pp(conclusions[i], m) << std::endl;
                    // }
                // }
                // SASSERT(at_least_one_changed);
                // if (!at_least_one_changed) {
                //     std::cout << "WARNING: NOTHING CHANGED!!!\n";
                // }
                // if (counter++ == 2) {
                //     return 0;
                // }
            } else {
                success = is_sat == l_false;
                break;
            }
        }
        if (!success) {
            return obj_hashtable<expr>();
        }
        obj_hashtable<expr> result;
        for (unsigned i = 0; i < enabled.size(); ++i) {
            if (enabled[i]) {
                result.insert(assumption_vars[i]);
            }
        }
        return result;
    }

    void mk_synchronize::disable_minimal_unsatisfiable_subset(expr_ref_vector const & set, model_ref const & model, svector<bool> & enabled) {
        smt::kernel solver(m, m_smt_params);
        // std::cout << "EXTRACTING MINIMAL UNSATISFIABLE SUBSET...\n";
        unsigned delta = 0;
        sort * bs = m.mk_bool_sort();
        ptr_vector<expr> exprs = replace_vars_with_consts(m, delta, set.size(), set.c_ptr());
        expr_ref_vector assumptions(m);
        obj_map<expr, unsigned> assumptions2idx;
        for (unsigned i = 0; i < exprs.size(); ++i) {
            if (enabled[i]) {
                // std::cout << "ASSERTING " << mk_pp(exprs[i], m) << std::endl;
                expr_ref valuation(m);
                if (model->eval(exprs[i], valuation)) {
                    expr * assumption = m.mk_fresh_const("__asmpt", bs);
                    assumptions.push_back(assumption);
                    assumptions2idx.insert(assumption, i);
                    solver.assert_expr(m.mk_implies(assumption, valuation));
                }
            }
        }
        lbool lresult = solver.check(assumptions);
        SASSERT(lresult == l_false);
        // std::cout << "RESULT IS " << lresult << "; GOT UNSAT CORE OF SIZE " << solver.get_unsat_core_size() << std::endl;
        for (unsigned i = 0; i < solver.get_unsat_core_size(); ++i) {
            expr * core_assumption = solver.get_unsat_core_expr(i);
            SASSERT(assumptions2idx.contains(core_assumption));
            enabled[assumptions2idx[core_assumption]] = false;
        }
    }

    void mk_synchronize::update_reachability_graph(func_decl * new_rel, ptr_vector<app> const & apps, rule * old_rule, rule * new_rule, rule_set & rules) {
        obj_hashtable<func_decl> orig_decls;
        for (ptr_vector<app>::const_iterator it = apps.begin(); it != apps.end(); ++it) {
            orig_decls.insert((*it)->get_decl());
        }
        rule_vector const & new_rules = rules.get_predicate_rules(new_rel);
        rule_reachability_graph::item_set const & deps = m_graph->get_deps(old_rule);
        for (rule_vector::const_iterator it = new_rules.begin(); it != new_rules.end(); ++it) {
            rule * prod = *it;
            bool depends = true;
            rule_vector const & orig_rules = *m_prod2orig[prod];
            for (rule_vector::const_iterator it2 = orig_rules.begin(); it2 != orig_rules.end(); ++it2) {
                if (!deps.contains(get_original_rule(*it2))) {
                    depends = false;
                    break;
                }
            }
            if (depends) {
                m_graph->connect(new_rule, prod);
            }
        }
        for (rule_reachability_graph::item_set::iterator it = deps.begin(); it != deps.end(); ++it) {
            if (!orig_decls.contains((*it)->get_head()->get_decl())) {
                m_graph->connect(new_rule, *it);
            }
        }
    }

    void mk_synchronize::update_reachability_graph(func_decl * new_rel, rule_set & rules) {
        rule_vector const & new_rules = rules.get_predicate_rules(new_rel);
        for (rule_vector::const_iterator it = new_rules.begin(); it != new_rules.end(); ++it) {
            rule * prod = *it;
            std::set<rule*> recursive_deps;
            bool initialized_recursive_deps = false;
            rule_vector const & orig_rules = *m_prod2orig[prod];
            for (unsigned i = 0; i < orig_rules.size(); ++i) {
                rule * orig = get_original_rule(orig_rules[i]);
                std::set<rule*> candidate_recursive_deps;
                rule_reachability_graph::item_set const & deps = m_graph->get_deps(orig);
                for (rule_reachability_graph::item_set::iterator it2 = deps.begin(); it2 != deps.end(); ++it2) {
                    rule * dep = *it2;
                    if (dep->get_head()->get_decl() == orig->get_head()->get_decl()) {
                        std::pair<unsigned, rule*> key(i, dep);
                        SASSERT(m_orig2prod.find(key) != m_orig2prod.end());
                        std::set<rule*> products_of_dep = *m_orig2prod[key];
                        candidate_recursive_deps.insert(products_of_dep.begin(), products_of_dep.end());
                    } else {
                        m_graph->connect(prod, dep);
                    }
                }
                if (!initialized_recursive_deps) {
                    recursive_deps = candidate_recursive_deps;
                    initialized_recursive_deps = true;
                } else {
                    std::set<rule*> tmp;
                    set_intersection(recursive_deps.begin(), recursive_deps.end(), candidate_recursive_deps.begin(), candidate_recursive_deps.end(), std::inserter(tmp, tmp.begin()));
                    recursive_deps = tmp;
                }
            }
            for (std::set<rule*>::const_iterator it2 = recursive_deps.begin(); it2 != recursive_deps.end(); ++it2) {
                m_graph->connect(prod, *it2);
            }
        }
    }

    void mk_synchronize::propagate_constraint(rule & r, app * non_rec_app, rule_set & rules) {
        m_stratifier = alloc(reachability_stratifier, *m_graph);
        if (!m_stratifier->validate_mutual_recursion()) {
            return;
        }

        reachability_stratifier::comp_vector const & strata = m_stratifier->get_strats();
        ptr_addr_map<reachability_stratifier::item_set, lemma *> strata2lemmas;
        for (unsigned i = strata.size(); i > 0; --i) {
            reachability_stratifier::item_set & stratum = *strata[i-1];
            if (stratum.contains(&r)) {
                SASSERT(strata2lemmas.empty());
                lemma * source_lemma = mine_lemma_from_rule(r, non_rec_app);
                strata2lemmas.insert(&stratum, source_lemma);
                // for (reachability_stratifier::item_set::iterator it = stratum.begin(); it != stratum.end(); ++it) {
                //     std::cout << (*it)->name() << " ";
                // }
                // std::cout << std::endl;
                // std::cout << "--------------------------------\n";
                // std::cout << "a. for stratum ";
                // reachability_stratifier::item_set & s = stratum;
                // for (reachability_stratifier::item_set::iterator it = s.begin(); it != s.end(); ++it) {
                //     std::cout << (*it)->name() << " ";
                // }
                // std::cout << "got\n";
                // source_lemma->display(std::cout);
                // std::cout << "--------------------------------\n";
            } else if (!stratum.empty() && (*stratum.begin())->get_head()->get_decl() == non_rec_app->get_decl() && !m_stratifier->is_non_recursive_stratum(stratum)) {
                ptr_vector<expr> assumption_vars, conclusions;
                ptr_vector<lemma> source_lemmas;
                for (ptr_addr_map<reachability_stratifier::item_set, lemma *>::iterator it = strata2lemmas.begin(); it != strata2lemmas.end(); ++it) {
                    if (m_stratifier->strata_connected(*(it->m_key), stratum)) {
                        source_lemmas.push_back(strata2lemmas[it->m_key]);
                    }
                }
                lemma * source_lemma = alloc(lemma, m, source_lemmas);
                ptr_vector<sort> free_var_sorts;
                svector<symbol> free_var_names;
                expr_ref_vector e = (*source_lemma)(stratum, assumption_vars, conclusions, free_var_sorts, free_var_names);
                free_var_names.reverse();
                free_var_sorts.reverse();
                obj_hashtable<expr> invariant = extract_invariant(e, assumption_vars, conclusions, free_var_sorts, free_var_names);
                lemma * resulting_lemma = alloc(lemma, m, *source_lemma, assumption_vars, invariant);
                // for (reachability_stratifier::item_set::iterator it = stratum.begin(); it != stratum.end(); ++it) {
                //     std::cout << (*it)->name() << " ";
                // }
                // std::cout << std::endl;
                strata2lemmas.insert(&stratum, resulting_lemma);
                // std::cout << "--------------------------------\n";
                // std::cout << "b. for stratum ";
                // reachability_stratifier::item_set &s = stratum;
                // for (reachability_stratifier::item_set::iterator it = s.begin(); it != s.end(); ++it) {
                //     std::cout << (*it)->name() << " ";
                // }
                // std::cout << "got\n";
                // resulting_lemma->display(std::cout);
                // std::cout << "--------------------------------\n";
            }
        }
        for (unsigned i = strata.size(); i > 0; --i) {
            reachability_stratifier::item_set & stratum = *strata[i-1];
            if (!stratum.empty() && (*stratum.begin())->get_head()->get_decl() == non_rec_app->get_decl() && !m_stratifier->is_non_recursive_stratum(stratum)) {
                lemma * resulting_lemma = strata2lemmas[&stratum];
                for (reachability_stratifier::item_set::iterator it = stratum.begin(); it != stratum.end(); ++it) {
                    // std::cout << "================================ENRICHING RULE " << (*it)->name() << ":" << std::endl;
                    // std::cout << "BEFORE:\n";
                    // (*it)->display(m_ctx, std::cout);
                    rule_ref new_rule = resulting_lemma->enrich_rule(**it, rules);
                    // std::cout << "AFTER:\n";
                    // new_rule->display(m_ctx, std::cout);
                }
            }
        }
    }

    app * mk_synchronize::product_application(ptr_vector<app> const & apps, func_decl * pred) {
        ptr_vector<app>::const_iterator it = apps.begin(), end = apps.end();
        unsigned args_num = 0;
        for (; it != end; ++it) {
            args_num += (*it)->get_num_args();
        }
        ptr_vector<expr> args;
        args.resize(args_num);
        it = apps.begin();
        for (unsigned args_idx = 0; it != end; ++it) {
            app* a = *it;
            for (unsigned i = 0; i < a->get_num_args(); ++i, ++args_idx) {
                args[args_idx] = a->get_arg(i);
            }
        }

        return m.mk_app(pred, args_num, args.c_ptr());
    }

    rule_ref mk_synchronize::make_tautoligocal_rule(func_decl * d, unsigned start_idx) {
        ptr_vector<expr> args;
        args.resize(d->get_arity());
        for (unsigned i = 0; i < d->get_arity(); ++i) {
            sort * s = d->get_domain(i);
            args[i] = m.mk_var(i + start_idx, s);
        }
        app * premise = m.mk_app(d, args.size(), args.c_ptr());
        app * conclusion = m.mk_app(d, args.size(), args.c_ptr());
        bool neg = false;
        rule_ref new_rule(rm);
        new_rule = rm.mk(conclusion, 1, &premise, &neg, symbol("TAUTO"), false);
        return new_rule;
    }

    rule_ref mk_synchronize::best_product_rule(rule_vector const & rules, func_decl * pred, lemma * source_lemma) {
        svector<unsigned> weights;
        ptr_vector<lemma> lemmas;
        if (rules.size() != 2) {
            std::cout << "AHTUNG! 2 RULES EXPECTED IN BEST PRODUCT RULE!!!\n";
            return rule_ref(rm);
        }

        rule * r1 = rules[0];
        ptr_vector<sort> sorts;
        r1->get_vars(m, sorts);
        rule * r2 = rules[1];
        rule * r1_tauto = make_tautoligocal_rule(r1->get_head()->get_decl(), 0).steal();
        rule * r2_tauto = make_tautoligocal_rule(r2->get_head()->get_decl(), sorts.size()).steal();
        svector<rule_ref> variants;
        svector<unsigned> ws; ws.push_back(2);
        rule_vector r12_src; r12_src.push_back(r1); r12_src.push_back(r2);
        rule_ref r12 = product_rule(r12_src, pred);
        variants.push_back(r12);
        if (!is_non_recursive_rule(*r1)) {
            rule_vector r1t2_src; r1t2_src.push_back(r1_tauto); r1t2_src.push_back(r2);
            rule_ref r1t2 = product_rule(r1t2_src, pred);
            variants.push_back(r1t2);
            ws.push_back(1);
        }
        if (!is_non_recursive_rule(*r2)) {
            rule_vector r12t_src; r12t_src.push_back(r1); r12t_src.push_back(r2_tauto);
            rule_ref r12t = product_rule(r12t_src, pred);
            variants.push_back(r12t);
            ws.push_back(1);
        }
        unsigned max_w = 0; unsigned max_idx = 0;

        for (unsigned i = 0; i < variants.size(); ++i) {
            obj_hashtable<rule> stratum;
            stratum.insert(variants[i].get());
                ptr_vector<expr> assumption_vars, conclusions;
                ptr_vector<sort> free_var_sorts;
                svector<symbol> free_var_names;
                variants[i]->display(m_ctx, std::cout);
                expr_ref_vector e = (*source_lemma)(stratum, assumption_vars, conclusions, free_var_sorts, free_var_names);
                free_var_names.reverse();
                free_var_sorts.reverse();
                obj_hashtable<expr> invariant = extract_invariant(e, assumption_vars, conclusions, free_var_sorts, free_var_names);
                lemma * resulting_lemma = alloc(lemma, m, *source_lemma, assumption_vars, invariant);
                unsigned lw = resulting_lemma->weight();
                unsigned w = lw;// * ws[i];
                std::cout << "FOR " << variants[i]->name() << " GOT LEMMA WEIGHT " << lw;// << " AND WEIGHT " << lw * ws[i];
                if (w > max_w) {
                    std::cout << "... AND THIS IS THE BEST WEIGHT!";
                    max_w = w;
                    max_idx = i;
                }
                std::cout << std::endl;
        }
        std::cout << "FINALLY GOT BEST IDX " << max_idx << " -------------------" << std::endl;
        return variants[max_idx];
    }

    rule_ref mk_synchronize::product_rule(rule_vector const & rules, func_decl * pred) {
        unsigned n = rules.size();

        string_buffer<> buffer;
        bool first_rule = true;
        for (rule_vector::const_iterator it = rules.begin(); it != rules.end(); ++it, first_rule = false) {
            if (!first_rule) {
                buffer << "+";
            }
            buffer << (*it)->name();
        }

        ptr_vector<app> heads;
        heads.resize(n);
        for (unsigned i = 0; i < rules.size(); ++i) {
            heads[i] = rules[i]->get_head();
        }
        app* product_head = product_application(heads, pred);

        unsigned product_tail_length = 0;
        bool has_recursion = false;
        vector< ptr_vector<app> > recursive_calls;
        recursive_calls.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            rule& rule = *rules[i];
            product_tail_length += rule.get_tail_size();
            for (unsigned j = 0; j < rule.get_positive_tail_size(); ++j) {
                app* tail = rule.get_tail(j);
                if (is_recursive_app(rule, tail)) {
                    has_recursion = true;
                    recursive_calls[i].push_back(tail);
                }
            }
            if (recursive_calls[i].empty()) {
                recursive_calls[i].push_back(rule.get_head());
            }
        }

        ptr_vector<app> new_tail;
        svector<bool> new_tail_neg;
        new_tail.resize(product_tail_length);
        new_tail_neg.resize(product_tail_length);
        unsigned tail_idx = -1;
        if (has_recursion) {
            // TODO: there may be more than one recursive call!
            ptr_vector<app> unique_recursive_calls;
            unique_recursive_calls.resize(n);
            for (unsigned i = 0; i < n; ++i) {
                unique_recursive_calls[i] = recursive_calls[i][0];
            }

            ++tail_idx;
            new_tail[tail_idx] = product_application(unique_recursive_calls, pred);
            new_tail_neg[tail_idx] = false;
        }

        for (rule_vector::const_iterator it = rules.begin(); it != rules.end(); ++it) {
            rule& rule = **it;
            for (unsigned i = 0; i < rule.get_positive_tail_size(); ++i) {
                app* tail = rule.get_tail(i);
                if (!is_recursive_app(rule, tail)) {
                    ++tail_idx;
                    new_tail[tail_idx] = tail;
                    new_tail_neg[tail_idx] = false;
                }
            }
            for (unsigned i = rule.get_positive_tail_size(); i < rule.get_uninterpreted_tail_size(); ++i) {
                ++tail_idx;
                new_tail[tail_idx] = rule.get_tail(i);
                new_tail_neg[tail_idx] = true;
            }
            for (unsigned i = rule.get_uninterpreted_tail_size(); i < rule.get_tail_size(); ++i) {
                ++tail_idx;
                new_tail[tail_idx] = rule.get_tail(i);
                new_tail_neg[tail_idx] = rule.is_neg_tail(i);
            }
        }

        rule_ref new_rule(rm);
        new_rule = rm.mk(product_head, tail_idx + 1,
            new_tail.c_ptr(), new_tail_neg.c_ptr(), symbol(buffer.c_str()), false);
        rm.fix_unbound_vars(new_rule, false);
        return new_rule;
    }

    void mk_synchronize::merge_rules(unsigned idx, ptr_vector<func_decl> const & decls, rule_vector &buf,
            vector<rule_vector> const & merged_rules, rule_set & all_rules, func_decl * pred, lemma * source_lemma) {
        if (idx >= decls.size()) {
            // rule_ref product = product_rule(buf, pred);
            rule_ref product = best_product_rule(buf, pred, source_lemma);
            m_prod2orig.insert(product.get(), alloc(rule_vector, buf));
            for (unsigned i = 0; i < buf.size(); ++i) {
                std::pair<unsigned, rule*> key(i, get_original_rule(buf[i]));
                std::set<rule*>* prods = 0;
                std::map<std::pair<unsigned, rule*>, std::set<rule*> *>::iterator e = m_orig2prod.find(key);
                if (e == m_orig2prod.end()) {
                    prods = alloc(std::set<rule*>);
                    m_orig2prod.insert(e, std::pair<std::pair<unsigned, rule*>, std::set<rule*>*>(key, prods));
                } else {
                    prods = m_orig2prod[key];
                }
                prods->insert(product.get());
            }
            all_rules.add_rule(product.get());
            return;
        }

        rule_vector const & pred_rules = merged_rules[idx];
        for (rule_vector::const_iterator it = pred_rules.begin(); it != pred_rules.end(); ++it) {
            buf[idx] = *it;
            merge_rules(idx + 1, decls, buf, merged_rules, all_rules, pred, source_lemma);
        }
    }

    rule_ref mk_synchronize::merge_applications(rule & r, rule_set & rules, ptr_vector<app> const & merged_apps, app *& resulting_app) {
        string_buffer<> buffer;
        ptr_vector<sort> domain;
        ptr_vector<app>::const_iterator it = merged_apps.begin(), end = merged_apps.end();
        for (; it != end; ++it) {
            func_decl* decl = (*it)->get_decl();
            buffer << decl->get_name();
            buffer << "!!";
            domain.append(decl->get_arity(), decl->get_domain());
        }

        // TODO: do not forget to check rules.contains(func_decl)
        func_decl* orig = merged_apps[0]->get_decl();
        func_decl* product_pred = m_ctx.mk_fresh_head_predicate(symbol(buffer.c_str()),
            symbol::null, domain.size(), domain.c_ptr(), orig);

        ptr_vector<func_decl> merged_decls;
        rule_vector rules_buf;
        unsigned n = merged_apps.size();
        merged_decls.resize(n);
        rules_buf.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            merged_decls[i] = merged_apps[i]->get_decl();
        }

        vector<rule_vector> renamed_rules = rename_bound_vars(merged_decls, rules);

        rule_ref result = replace_applications(r, merged_apps, product_pred, resulting_app);
        rules.replace_rule(&r, result.get());

        lemma * source_lemma = mine_lemma_from_rule(*result.get(), resulting_app); // TODO: duplicate place!
        merge_rules(0, merged_decls, rules_buf, renamed_rules, rules, product_pred, source_lemma);

        update_reachability_graph(product_pred, rules);
        update_reachability_graph(product_pred, merged_apps, &r, result.get(), rules);

        return result;
        // propagate_constraint(*result.get(), resulting_app, rules);
        // reset_dealloc_values(m_prod2orig);
        // for (std::map<std::pair<unsigned, rule*>, std::set<rule*> *>::const_iterator it = m_orig2prod.begin(); it != m_orig2prod.end(); ++it) {
        //     dealloc(it->second);
        // }
        // m_orig2prod.clear();    
    }

    void mk_synchronize::merge_applications(rule & r, rule_set & rules) {
        ptr_vector<app> non_recursive_applications;
        for (unsigned i = 0; i < r.get_positive_tail_size(); ++i) {
            app* application = r.get_tail(i);
            // TODO: filter out merging applications of non-recursive relations...
            if (!is_recursive_app(r, application)) {
                non_recursive_applications.push_back(application);
            }
        }
        if (non_recursive_applications.size() < 2) {
            return;
        }

        // merge_applications(r, rules, non_recursive_applications);
        app * last_merge_result = non_recursive_applications[non_recursive_applications.size() - 1];
        rule_ref result(rm);
        for (unsigned i = non_recursive_applications.size() - 1; i > 0; --i) {
            app * a = non_recursive_applications[i - 1];
            ptr_vector<app> apps;
            apps.push_back(a);
            apps.push_back(last_merge_result);
            std::cout << "--------- SELECTING BEST PRODUCT OF";
            for (unsigned i = 0; i < apps.size(); ++i) {
                std::cout << " " << mk_pp(apps[i], m);
            }
            std::cout << std::endl;
            result = merge_applications(r, rules, apps, last_merge_result);
        }

        propagate_constraint(*result.get(), last_merge_result, rules);
        reset_dealloc_values(m_prod2orig);
        for (std::map<std::pair<unsigned, rule*>, std::set<rule*> *>::const_iterator it = m_orig2prod.begin(); it != m_orig2prod.end(); ++it) {
            dealloc(it->second);
        }
        m_orig2prod.clear();    
    }

    void mk_synchronize::tautologically_extend(rule_set & rules, ptr_vector<func_decl> const & decls) {
        for (ptr_vector<func_decl>::const_iterator it = decls.begin(); it != decls.end(); ++it) {
            func_decl * d = *it;
            ptr_vector<expr> args;
            args.resize(d->get_arity());
            for (unsigned i = 0; i < d->get_arity(); ++i) {
                sort * s = d->get_domain(i);
                args[i] = m.mk_var(i, s);
            }
            app * premise = m.mk_app(d, args.size(), args.c_ptr());
            app * conclusion = m.mk_app(d, args.size(), args.c_ptr());
            bool neg = false;
            rule_ref new_rule(rm);
            new_rule = rm.mk(conclusion, 1, &premise, &neg, symbol("TAUTO"), false);
            rules.add_rule(new_rule.get());
        }
    }

    rule_set * mk_synchronize::operator()(rule_set const & source) {
        printf("\n\n----------------------------------\nSYNCHRONIZING! SOURCE RULES:\n");
        source.display(std::cout);

        rule_set* rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);

        rule_set::iterator it = source.begin(), end = source.end();
        for (; it != end; ++it) {
            rules->add_rule(*it);
        }

        m_graph = alloc(rule_reachability_graph, m_ctx, *rules);

        // ptr_vector<func_decl> decls;
        // for (rule_set::decl2rules::iterator it = rules->begin_grouped_rules(); it != rules->end_grouped_rules(); ++it) {
        //     decls.push_back(it->m_key);
        // }
        // tautologically_extend(*rules, decls);

        unsigned current_rule = 0;
        while (current_rule < rules->get_num_rules()) {
            rule *r = rules->get_rule(current_rule);
            merge_applications(*r, *rules);
            ++current_rule;
        }

        // printf("\n-----------------DEPENDENCIES GRAPH-----------------\n");
        // m_stratifier = alloc(reachability_stratifier, *m_graph);
        // m_stratifier->display(std::cout);
        // if (!m_stratifier->validate_mutual_recursion()) {
        //     return rules;
        // }
        // printf("\n------------------------------------------------------------\n");

        printf("\n\n-----------------RESULTING RULES:-----------------\n");
        rules->display(std::cout);
        printf("\n\n----------------------------------\n");
        return rules;
    }

};
