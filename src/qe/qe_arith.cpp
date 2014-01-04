/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    qe_arith.cpp

Abstract:

    Simple projection function for real arithmetic based on Loos-W.

Author:

    Nikolaj Bjorner (nbjorner) 2013-09-12

Revision History:


--*/

#include "qe_arith.h"
#include "qe_util.h"
#include "qe.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"
#include "th_rewriter.h"
#include "expr_functors.h"
#include "expr_substitution.h"
#include "expr_replacer.h"

namespace qe {

    class is_relevant_default : public i_expr_pred {
    public:
        bool operator()(expr* e) {
            return true;
        }
    };

    class mk_atom_default : public i_nnf_atom {
    public:
        virtual void operator()(expr* e, bool pol, expr_ref& result) {
            if (pol) result = e; 
            else result = result.get_manager().mk_not(e);
        }
    };

    class arith_project_util {
        ast_manager& m;
        arith_util   a;
        th_rewriter  m_rw;
        expr_ref_vector  m_lits;
        expr_ref_vector  m_terms;
        vector<rational> m_coeffs;
        vector<rational> m_divs;
        svector<bool>    m_strict;
        svector<bool>    m_eq;
        scoped_ptr<contains_app> m_var;

        struct cant_project {};

        void is_linear(rational const& mul, expr* t, rational& c, expr_ref_vector& ts) {
            expr* t1, *t2;
            rational mul1;
            if (t == m_var->x()) {
                c += mul;
            }
            else if (a.is_mul(t, t1, t2) && a.is_numeral(t1, mul1)) {
                is_linear(mul* mul1, t2, c, ts);
            }
            else if (a.is_mul(t, t1, t2) && a.is_numeral(t2, mul1)) {
                is_linear(mul* mul1, t1, c, ts);
            }
            else if (a.is_add(t)) {
                app* ap = to_app(t);
                for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                    is_linear(mul, ap->get_arg(i), c, ts);
                }
            }
            else if (a.is_sub(t, t1, t2)) {
                is_linear(mul,  t1, c, ts);
                is_linear(-mul, t2, c, ts);
            }
            else if (a.is_uminus(t, t1)) {
                is_linear(-mul, t1, c, ts);
            }
            else if (a.is_numeral(t, mul1)) {
                ts.push_back(a.mk_numeral(mul*mul1, m.get_sort(t)));
            }
            else if ((*m_var)(t)) {
                IF_VERBOSE(1, verbose_stream() << "can't project:" << mk_pp(t, m) << "\n";);
                throw cant_project();
            }
            else if (mul.is_one()) {
                ts.push_back(t);
            }
            else {
                ts.push_back(a.mk_mul(a.mk_numeral(mul, m.get_sort(t)), t));
            }
        }

        // either an equality (cx + t = 0) or an inequality (cx + t <= 0) or a divisibility literal (d | cx + t)
        bool is_linear(expr* lit, rational& c, expr_ref& t, rational& d, bool& is_strict, bool& is_eq, bool& is_diseq) {
            if (!(*m_var)(lit)) {
                return false;
            }
            expr* e1, *e2;
            c.reset();
            sort* s;
            expr_ref_vector ts(m);            
            bool is_not = m.is_not(lit, lit);
            rational mul(1);
            if (is_not) {
                mul.neg();
            }
            SASSERT(!m.is_not(lit));
            if (a.is_le(lit, e1, e2) || a.is_ge(lit, e2, e1)) {
                is_linear( mul, e1, c, ts);
                is_linear(-mul, e2, c, ts);
                s = m.get_sort(e1);
                is_strict = is_not;
            }
            else if (a.is_lt(lit, e1, e2) || a.is_gt(lit, e2, e1)) {
                is_linear( mul, e1, c, ts);
                is_linear(-mul, e2, c, ts);
                s = m.get_sort(e1);
                is_strict = !is_not;
            }
            else if (m.is_eq(lit, e1, e2)) {
                expr *t, *num;
                rational num_val, d_val, z;
                bool is_int;
                if (a.is_mod (e1, t, num) && a.is_numeral (num, num_val, is_int) && is_int &&
                        a.is_numeral (e2, z) && z.is_zero ()) {
                    // divsibility constraint: t % num == 0 <=> num | t
                    if (num_val.is_zero ()) {
                        IF_VERBOSE(1, verbose_stream() << "div by zero" << mk_pp(lit, m) << "\n";);
                        throw cant_project();
                    }
                    d = num_val;
                    is_linear (mul, t, c, ts);
                } else if (a.is_mod (e2, t, num) && a.is_numeral (num, num_val, is_int) && is_int &&
                        a.is_numeral (e1, z) && z.is_zero ()) {
                    // divsibility constraint: 0 == t % num <=> num | t
                    if (num_val.is_zero ()) {
                        IF_VERBOSE(1, verbose_stream() << "div by zero" << mk_pp(lit, m) << "\n";);
                        throw cant_project();
                    }
                    d = num_val;
                    is_linear (mul, t, c, ts);
                } else {
                    // equality or disequality
                    is_linear( mul, e1, c, ts);
                    is_linear(-mul, e2, c, ts);
                    if (is_not) is_diseq = true;
                    else is_eq = true;
                }
                s = m.get_sort(e1);
            }
            else {
                IF_VERBOSE(1, verbose_stream() << "can't project:" << mk_pp(lit, m) << "\n";);
                throw cant_project();
            }

            if (ts.empty()) {
                t = a.mk_numeral(rational(0), s);
            }
            else {
                t = a.mk_add(ts.size(), ts.c_ptr());
            }

            return true;
        }

        void project(model& mdl, expr_ref_vector& lits) {
            unsigned num_pos = 0;
            unsigned num_neg = 0;
            bool use_eq = false;
            expr_ref_vector new_lits(m);
            expr_ref eq_term (m);

            m_lits.reset ();
            m_terms.reset();
            m_coeffs.reset();
            m_strict.reset();
            m_eq.reset ();

            for (unsigned i = 0; i < lits.size(); ++i) {
                rational c(0), d(0);
                expr_ref t(m);
                bool is_strict = false;
                bool is_eq = false;
                bool is_diseq = false;
                if (is_linear(lits.get (i), c, t, d, is_strict, is_eq, is_diseq)) {
                    if (c.is_zero()) {
                        m_rw(lits.get (i), t);
                        new_lits.push_back(t);
                    } else if (is_eq) {
                        if (!use_eq) {
                            // c*x + t = 0  <=>  x = -t/c
                            eq_term = mk_mul (-(rational::one ()/c), t);
                            use_eq = true;
                        }
                        m_lits.push_back (lits.get (i));
                        m_coeffs.push_back(c);
                        m_terms.push_back(t);
                        m_strict.push_back(false);
                        m_eq.push_back (true);
                    } else {
                        if (is_diseq) {
                            // c*x + t != 0
                            // find out whether c*x + t < 0, or c*x + t > 0
                            expr_ref cx (m), cxt (m), val (m);
                            rational r;
                            cx = mk_mul (c, m_var->x());
                            cxt = mk_add (cx, t);
                            VERIFY(mdl.eval(cxt, val, true));
                            VERIFY(a.is_numeral(val, r));
                            SASSERT (r > rational::zero () || r < rational::zero ());
                            if (r > rational::zero ()) {
                                c = -c;
                                t = mk_mul (-(rational::one()), t);
                            }
                            is_strict = true;
                        }
                        m_lits.push_back (lits.get (i));
                        m_coeffs.push_back(c);
                        m_terms.push_back(t);
                        m_strict.push_back(is_strict);
                        m_eq.push_back (false);
                        if (c.is_pos()) {
                            ++num_pos;
                        }
                        else {
                            ++num_neg;
                        }                    
                    }
                }
                else {
                    new_lits.push_back(lits.get (i));
                }
            }
            if (use_eq) {
                TRACE ("qe",
                        tout << "Using equality term: " << mk_pp (eq_term, m) << "\n";
                      );
                // substitute eq_term for x everywhere
                for (unsigned i = 0; i < m_lits.size(); ++i) {
                    expr_ref cx (m), cxt (m), z (m), result (m);
                    cx = mk_mul (m_coeffs[i], eq_term);
                    cxt = mk_add (cx, m_terms.get(i));
                    z = a.mk_numeral(rational(0), m.get_sort(eq_term));
                    if (m_eq[i]) {
                        // c*x + t = 0
                        result = a.mk_eq (cxt, z);
                    } else if (m_strict[i]) {
                        // c*x + t < 0
                        result = a.mk_lt (cxt, z);
                    } else {
                        // c*x + t <= 0
                        result = a.mk_le (cxt, z);
                    }
                    m_rw (result);
                    new_lits.push_back (result);
                }
            }
            lits.reset();
            lits.append(new_lits);
            if (use_eq || num_pos == 0 || num_neg == 0) {
                return;
            }
            bool use_pos = num_pos < num_neg;
            unsigned max_t = find_max(mdl, use_pos);

            expr_ref new_lit (m);
            for (unsigned i = 0; i < m_lits.size(); ++i) {
                if (i != max_t) {
                    if (m_coeffs[i].is_pos() == use_pos) {
                        new_lit = mk_le(i, max_t);
                    }
                    else {
                        new_lit = mk_lt(i, max_t);
                    }
                    lits.push_back(new_lit);
                    TRACE ("qe",
                            tout << "Old literal: " << mk_pp (m_lits.get (i), m) << "\n";
                            tout << "New literal: " << mk_pp (new_lit, m) << "\n";
                          );
                }
            }
        }

        void project(model& mdl, app_ref_vector const& lits, expr_map& map, app_ref& div_lit) {
            unsigned num_pos = 0; // number of positive literals true in the model
            unsigned num_neg = 0; // number of negative literals true in the model

            m_lits.reset ();
            m_terms.reset();
            m_coeffs.reset();
            m_divs.reset ();
            m_strict.reset();
            m_eq.reset ();

            expr_ref var_val (m);
            VERIFY (mdl.eval (m_var->x(), var_val, true));

            unsigned eq_idx = lits.size ();
            for (unsigned i = 0; i < lits.size(); ++i) {
                rational c(0), d(0);
                expr_ref t(m);
                bool is_strict = false;
                bool is_eq = false;
                bool is_diseq = false;
                if (is_linear(lits.get (i), c, t, d, is_strict, is_eq, is_diseq)) {
                    TRACE ("qe",
                            tout << "Literal: " << mk_pp (lits.get (i), m) << "\n";
                          );

                    if (c.is_zero()) {
                        TRACE ("qe",
                                tout << "independent of variable\n";
                              );
                        continue;
                    }

                    // evaluate c*x + t in the model
                    expr_ref cx (m), cxt (m), val (m);
                    rational r;
                    cx = mk_mul (c, m_var->x());
                    cxt = mk_add (cx, t);
                    VERIFY(mdl.eval(cxt, val, true));
                    VERIFY(a.is_numeral(val, r));

                    if (is_eq) {
                        TRACE ("qe",
                                tout << "equality term\n";
                              );
                        // check if the equality is true in the mdl
                        if (eq_idx == lits.size () && r == rational::zero ()) {
                            eq_idx = m_lits.size ();
                        }
                        m_lits.push_back (lits.get (i));
                        m_coeffs.push_back(c);
                        m_terms.push_back(t);
                        m_strict.push_back(false);
                        m_eq.push_back (true);
                        m_divs.push_back (d);
                    } else {
                        TRACE ("qe",
                                tout << "not an equality term\n";
                              );
                        if (is_diseq) {
                            // c*x + t != 0
                            // find out whether c*x + t < 0, or c*x + t > 0
                            if (r > rational::zero ()) {
                                c = -c;
                                t = mk_mul (-(rational::one()), t);
                                r = -r;
                            }
                            // note: if the disequality is false in the model,
                            // r==0 and we end up choosing c*x + t < 0
                            is_strict = true;
                        }
                        m_lits.push_back (lits.get (i));
                        m_coeffs.push_back(c);
                        m_terms.push_back(t);
                        m_strict.push_back(is_strict);
                        m_eq.push_back (false);
                        m_divs.push_back (d);
                        if (d.is_zero ()) { // not a div term
                            if ((is_strict && r < rational::zero ()) ||
                                    (!is_strict && r <= rational::zero ())) { // literal true in the model
                                if (c.is_pos()) {
                                    ++num_pos;
                                }
                                else {
                                    ++num_neg;
                                }
                            }
                        }
                    }
                    TRACE ("qe",
                            tout << "c: " << c << "\n";
                            tout << "t: " << mk_pp (t, m) << "\n";
                            tout << "d: " << d << "\n";
                          );
                }
            }

            rational lcm_coeffs (1), lcm_divs (1);
            if (a.is_int (m_var->x())) {
                // lcm of (absolute values of) coeffs
                for (unsigned i = 0; i < m_lits.size (); i++) {
                    lcm_coeffs = lcm (lcm_coeffs, abs (m_coeffs[i]));
                }
                // normalize coeffs of x to +/-lcm_coeffs and scale terms and divs appropriately;
                // find lcm of scaled-up divs
                for (unsigned i = 0; i < m_lits.size (); i++) {
                    rational factor (lcm_coeffs / abs(m_coeffs[i]));
                    m_terms[i] = a.mk_mul (a.mk_numeral (factor, a.mk_int ()),
                                           m_terms.get (i));
                    m_coeffs[i] = (m_coeffs[i].is_pos () ? lcm_coeffs : -lcm_coeffs);
                    if (!m_divs[i].is_zero ()) {
                        m_divs[i] *= factor;
                        lcm_divs = lcm (lcm_divs, m_divs[i]);
                    }
                    TRACE ("qe",
                            tout << "normalized coeff: " << m_coeffs[i] << "\n";
                            tout << "normalized term: " << mk_pp (m_terms.get (i), m) << "\n";
                            tout << "normalized div: " << m_divs[i] << "\n";
                          );
                }

                // consider new divisibility literal (lcm_coeffs | (lcm_coeffs * x))
                lcm_divs = lcm (lcm_divs, lcm_coeffs);

                TRACE ("qe",
                        tout << "lcm of coeffs: " << lcm_coeffs << "\n";
                        tout << "lcm of divs: " << lcm_divs << "\n";
                      );
            }

            expr_ref z (a.mk_numeral (rational::zero (), a.mk_int ()), m);
            expr_ref x_term_val (m);

            // use equality term
            if (eq_idx < lits.size ()) {
                if (a.is_real (m_var->x ())) {
                    // c*x + t = 0  <=>  x = -t/c
                    expr_ref eq_term (mk_mul (-(rational::one ()/m_coeffs[eq_idx]), m_terms.get (eq_idx)), m);
                    m_rw (eq_term);
                    map.insert (m_var->x (), eq_term, 0);
                    TRACE ("qe",
                            tout << "Using equality term: " << mk_pp (eq_term, m) << "\n";
                          );
                }
                else {
                    // find substitution term for (lcm_coeffs * x)
                    if (m_coeffs[eq_idx].is_pos ()) {
                        x_term_val = a.mk_uminus (m_terms.get (eq_idx));
                    } else {
                        x_term_val = m_terms.get (eq_idx);
                    }
                    m_rw (x_term_val);
                    TRACE ("qe",
                            tout << "Using equality literal: " << mk_pp (m_lits.get (eq_idx), m) << "\n";
                            tout << "substitution for (lcm_coeffs * x): " << mk_pp (x_term_val, m) << "\n";
                          );
                    // can't simply substitute for x; need to explicitly substitute the lits
                    mk_lit_substitutes (x_term_val, map, eq_idx);

                    if (!lcm_coeffs.is_one ()) {
                        // new div constraint: lcm_coeffs | x_term_val
                        div_lit = m.mk_eq (a.mk_mod (x_term_val,
                                                     a.mk_numeral (lcm_coeffs, a.mk_int ())),
                                           z);
                    }
                }

                return;
            }

            expr_ref new_lit (m);

            if (num_pos == 0 || num_neg == 0) {
                TRACE ("qe",
                        tout << "virtual substitution of +/-infinity\n";
                      );

                /**
                 * make all equalities false;
                 * if num_pos = 0 (num_neg = 0), make all positive (negative) inequalities false;
                 * make the rest inequalities true;
                 * substitute value of x under given model for the rest (div terms)
                 */

                if (a.is_int (m_var->x())) {
                    // to substitute for (lcm_coeffs * x), it suffices to pick
                    // some element in the congruence class of (lcm_coeffs * x) mod lcm_divs;
                    // simply substituting var_val for x in the literals does this job;
                    // but to keep constants small, we use (lcm_coeffs * var_val) % lcm_divs instead
                    rational var_val_num;
                    VERIFY (a.is_numeral (var_val, var_val_num));
                    x_term_val = a.mk_numeral (mod (lcm_coeffs * var_val_num, lcm_divs),
                                               a.mk_int ());
                    TRACE ("qe",
                            tout << "Substitution for (lcm_coeffs * x):" << "\n";
                            tout << mk_pp (x_term_val, m) << "\n";
                          );
                }
                for (unsigned i = 0; i < m_lits.size (); i++) {
                    if (!m_divs[i].is_zero ()) {
                        // m_divs[i] | (x_term_val + m_terms[i])
                        new_lit = m.mk_eq (a.mk_mod (a.mk_add (m_terms.get (i), x_term_val),
                                                     a.mk_numeral (m_divs[i], a.mk_int ())),
                                           z);
                        m_rw (new_lit);
                    } else if (m_eq[i] ||
                               (num_pos == 0 && m_coeffs[i].is_pos ()) ||
                               (num_neg == 0 && m_coeffs[i].is_neg ())) {
                        new_lit = m.mk_false ();
                    } else {
                        new_lit = m.mk_true ();
                    }
                    map.insert (m_lits.get (i), new_lit, 0);
                    TRACE ("qe",
                            tout << "Old literal: " << mk_pp (m_lits.get (i), m) << "\n";
                            tout << "New literal: " << mk_pp (new_lit, m) << "\n";
                          );
                }
                return;
            }

            bool use_pos = num_pos < num_neg; // pick a side; both are sound

            unsigned max_t = find_max(mdl, use_pos);

            TRACE ("qe",
                    tout << "test point: " << mk_pp (m_lits.get (max_t), m) << "\n";
                  );

            if (a.is_real (m_var->x ())) {
                for (unsigned i = 0; i < m_lits.size(); ++i) {
                    if (i != max_t) {
                        if (m_eq[i]) {
                            if (!m_strict[max_t]) {
                                new_lit = mk_eq (i, max_t);
                            } else {
                                new_lit = m.mk_false ();
                            }
                        } else if (m_coeffs[i].is_pos() == use_pos) {
                            new_lit = mk_le (i, max_t);
                        } else {
                            new_lit = mk_lt (i, max_t);
                        }
                    } else {
                        new_lit = m.mk_true ();
                    }
                    map.insert (m_lits.get (i), new_lit, 0);
                    TRACE ("qe",
                            tout << "Old literal: " << mk_pp (m_lits.get (i), m) << "\n";
                            tout << "New literal: " << mk_pp (new_lit, m) << "\n";
                          );
                }
            } else {
                SASSERT (a.is_int (m_var->x ()));

                // mk substitution term for (lcm_coeffs * x)

                // evaluate c*x + t for the literal at max_t
                expr_ref cx (m), cxt (m), val (m);
                rational r;
                cx = mk_mul (m_coeffs[max_t], m_var->x());
                cxt = mk_add (cx, m_terms.get (max_t));
                VERIFY(mdl.eval(cxt, val, true));
                VERIFY(a.is_numeral(val, r));

                // get the offset from the smallest/largest possible value for x
                // literal      smallest/largest val of x
                // -------      --------------------------
                // l < x            l+1
                // l <= x            l
                // x < u            u-1
                // x <= u            u
                rational offset;
                if (m_strict[max_t]) {
                    offset = abs(r) - rational::one ();
                } else {
                    offset = abs(r);
                }
                // obtain the offset modulo lcm_divs
                offset %= lcm_divs;

                // for strict negative literal (i.e. strict lower bound),
                // substitution term is (t+1+offset); for non-strict, it's (t+offset)
                //
                // for positive term, subtract from 0
                x_term_val = mk_add (m_terms.get (max_t), a.mk_numeral (offset, a.mk_int ()));
                if (m_strict[max_t]) {
                    x_term_val = a.mk_add (x_term_val, a.mk_numeral (rational::one(), a.mk_int ()));
                }
                if (m_coeffs[max_t].is_pos ()) {
                    x_term_val = a.mk_uminus (x_term_val);
                }
                m_rw (x_term_val);

                TRACE ("qe",
                        tout << "substitution for (lcm_coeffs * x): " << mk_pp (x_term_val, m) << "\n";
                      );

                // obtain substitutions for all literals in map
                mk_lit_substitutes (x_term_val, map, max_t);

                if (!lcm_coeffs.is_one ()) {
                    // new div constraint: lcm_coeffs | x_term_val
                    div_lit = m.mk_eq (a.mk_mod (x_term_val,
                                                 a.mk_numeral (lcm_coeffs, a.mk_int ())),
                                       z);
                }
            }
        }

        unsigned find_max(model& mdl, bool do_pos) {
            unsigned result;
            bool found = false;
            bool found_strict = false;
            rational found_val (0), r, r_plus_x, found_c;
            expr_ref val(m);

            // evaluate x in mdl
            rational r_x;
            VERIFY(mdl.eval(m_var->x (), val, true));
            VERIFY(a.is_numeral (val, r_x));

            for (unsigned i = 0; i < m_terms.size(); ++i) {
                rational const& ac = m_coeffs[i];
                if (!m_eq[i] && ac.is_pos() == do_pos) {
                    VERIFY(mdl.eval(m_terms.get (i), val, true));
                    VERIFY(a.is_numeral(val, r));
                    r /= abs(ac);
                    // skip the literal if false in the model
                    if (do_pos) { r_plus_x = r + r_x; }
                    else { r_plus_x = r - r_x; }
                    if (!((m_strict[i] && r_plus_x < rational::zero ()) ||
                            (!m_strict[i] && r_plus_x <= rational::zero ()))) {
                        continue;
                    }
                    IF_VERBOSE(1, verbose_stream() << "max: " << mk_pp(m_terms.get (i), m) << " " << r << " " <<
                                (!found || r > found_val || (r == found_val && !found_strict && m_strict[i])) << "\n";);
                    if (!found || r > found_val || (r == found_val && !found_strict && m_strict[i])) {
                        result = i;
                        found_val = r;
                        found_c = ac;
                        found = true;
                        found_strict = m_strict[i];
                    }
                }
            }
            SASSERT(found);
            return result;
        }

        // ax + t <= 0
        // bx + s <= 0
        // a and b have different signs.
        // Infer: a|b|x + |b|t + |a|bx + |a|s <= 0
        // e.g.   |b|t + |a|s <= 0
        expr_ref mk_lt(unsigned i, unsigned j) {
            rational const& ac = m_coeffs[i];
            rational const& bc = m_coeffs[j];
            SASSERT(ac.is_pos() != bc.is_pos());
            SASSERT(ac.is_neg() != bc.is_neg());
            expr_ref bt (m), as (m), ts (m), z (m);
            expr* t = m_terms.get (i);
            expr* s = m_terms.get (j);
            bt = mk_mul(abs(bc), t);
            as = mk_mul(abs(ac), s);
            ts = mk_add(bt, as);
            z  = a.mk_numeral(rational(0), m.get_sort(t));
            expr_ref result1(m), result2(m);
            if (m_strict[i] || m_strict[j]) {
                result1 = a.mk_lt(ts, z);
            }
            else {
                result1 = a.mk_le(ts, z);
            }
            m_rw(result1, result2);
            return result2;
        }

        // ax + t <= 0
        // bx + s <= 0
        // a and b have same signs.
        // encode:// t/|a| <= s/|b|
        // e.g.   |b|t <= |a|s
        expr_ref mk_le(unsigned i, unsigned j) {
            rational const& ac = m_coeffs[i];
            rational const& bc = m_coeffs[j];
            SASSERT(ac.is_pos() == bc.is_pos());
            SASSERT(ac.is_neg() == bc.is_neg());
            expr_ref bt (m), as (m);
            expr* t = m_terms.get (i);
            expr* s = m_terms.get (j);
            bt = mk_mul(abs(bc), t);
            as = mk_mul(abs(ac), s);
            expr_ref result1(m), result2(m);
            if (!m_strict[j] && m_strict[i]) {
                result1 = a.mk_lt(bt, as);
            }
            else {
                result1 = a.mk_le(bt, as);
            }
            m_rw(result1, result2);
            return result2;
        }
        
        // ax + t = 0
        // bx + s <= 0
        // replace equality by (-t/a == -s/b), or, as = bt
        expr_ref mk_eq (unsigned i, unsigned j) {
            expr_ref as (m), bt (m);
            as = mk_mul (m_coeffs[i], m_terms.get (j));
            bt = mk_mul (m_coeffs[j], m_terms.get (i));
            expr_ref result (m);
            result = m.mk_eq (as, bt);
            m_rw (result);
            return result;
        }


        expr* mk_add(expr* t1, expr* t2) {
            return a.mk_add(t1, t2);
        }
        expr* mk_mul(rational const& r, expr* t2) {
            expr* t1 = a.mk_numeral(r, m.get_sort(t2));
            return a.mk_mul(t1, t2);
        }

        /**
         * factor out mod terms by using divisibility terms;
         *
         * for now, only handle mod equalities of the form (t1 % num == t2),
         * replacing it by the equivalent (num | (t1-t2)) /\ (0 <= t2 < abs(num));
         * the divisibility atom is a special mod term ((t1-t2) % num == 0)
         *
         * TODO: to handle arbitrary terms containing mod sub-terms, we can
         * introduce temporary auxiliary variables and eliminate them at the end
         */
        void mod2div (expr_ref& fml, expr_map& map) {
            expr* new_fml = 0;

            proof *pr = 0;
            map.get (fml, new_fml, pr);
            if (new_fml) {
                fml = new_fml;
                return;
            }

            expr_ref z (a.mk_numeral (rational::zero (), a.mk_int ()), m);
            bool is_mod_eq = false;

            expr *e1, *e2, *num;
            expr_ref t1 (m), t2 (m);
            rational num_val;
            bool is_int;
            // check if fml is a mod equality (t1 % num) == t2
            if (m.is_eq (fml, e1, e2)) {
                expr* t;
                if (a.is_mod (e1, t, num) && a.is_numeral (num, num_val, is_int) && is_int) {
                    t1 = t;
                    t2 = e2;
                    is_mod_eq = true;
                } else if (a.is_mod (e2, t, num) && a.is_numeral (num, num_val, is_int) && is_int) {
                    t1 = t;
                    t2 = e1;
                    is_mod_eq = true;
                }
            }

            if (is_mod_eq) {
                // recursively mod2div for t1 and t2
                mod2div (t1, map);
                mod2div (t2, map);

                rational t2_num;
                if (a.is_numeral (t2, t2_num) && t2_num.is_zero ()) {
                    // already in the desired form;
                    // new_fml is (num_val | t1)
                    new_fml = m.mk_eq (a.mk_mod (t1, a.mk_numeral (num_val, a.mk_int ())),
                                       z);
                }
                else {
                    expr_ref_vector lits (m);
                    // num_val | (t1 - t2)
                    lits.push_back (m.mk_eq (a.mk_mod (a.mk_sub (t1, t2),
                                                    a.mk_numeral (num_val, a.mk_int ())),
                                          z));
                    // 0 <= t2
                    lits.push_back (a.mk_le (z, t2));
                    // t2 < abs (num_val)
                    lits.push_back (a.mk_lt (t2, a.mk_numeral (abs (num_val), a.mk_int ())));

                    new_fml = m.mk_and (lits.size (), lits.c_ptr ());
                }
            }
            else if (!is_app (fml)) {
                new_fml = fml;
            }
            else {
                app* a = to_app (fml);
                expr_ref_vector children (m);
                expr_ref ch (m);
                for (unsigned i = 0; i < a->get_num_args (); i++) {
                    ch = a->get_arg (i);
                    mod2div (ch, map);
                    children.push_back (ch);
                }
                new_fml = m.mk_app (a->get_decl (), children.size (), children.c_ptr ());
            }

            map.insert (fml, new_fml, 0);
            fml = new_fml;
        }

        void collect_lits (expr* fml, app_ref_vector& lits) {
            expr_ref_vector todo (m);
            ast_mark visited;
            todo.push_back(fml);
            while (!todo.empty()) {
                expr* e = todo.back();
                todo.pop_back();
                if (visited.is_marked(e)) {
                    continue;
                }
                visited.mark(e, true);
                if (!is_app(e)) {
                    continue;
                }
                app* a = to_app(e);
                if (m.is_and(a) || m.is_or(a)) {
                    for (unsigned i = 0; i < a->get_num_args(); ++i) {
                        todo.push_back(a->get_arg(i));
                    }
                } else {
                    lits.push_back (a);
                }
            }
            SASSERT(todo.empty());
            visited.reset();
        }

        /**
         * assume that all coeffs of x are the same, say c
         * substitute x_term_val for (c*x) in all lits and update map
         * make the literal at idx true
         */
        void mk_lit_substitutes (expr_ref const& x_term_val, expr_map& map, unsigned idx) {
            expr_ref z (a.mk_numeral (rational::zero (), a.mk_int ()), m);
            expr_ref cxt (m), new_lit (m);
            for (unsigned i = 0; i < m_lits.size(); ++i) {
                if (i == idx) {
                    new_lit = m.mk_true ();
                } else {
                    // cxt
                    if (m_coeffs[i].is_neg ()) {
                        cxt = a.mk_sub (m_terms.get (i), x_term_val);
                    } else {
                        cxt = a.mk_add (m_terms.get (i), x_term_val);
                    }

                    if (m_divs[i].is_zero ()) {
                        if (m_eq[i]) {
                            new_lit = m.mk_eq (cxt, z);
                        } else if (m_strict[i]) {
                            new_lit = a.mk_lt (cxt, z);
                        } else {
                            new_lit = a.mk_le (cxt, z);
                        }
                    } else {
                        // div term
                        new_lit = m.mk_eq (a.mk_mod (cxt,
                                                     a.mk_numeral (m_divs[i], a.mk_int ())),
                                           z);
                    }
                }
                map.insert (m_lits.get (i), new_lit, 0);
                TRACE ("qe",
                        tout << "Old literal: " << mk_pp (m_lits.get (i), m) << "\n";
                        tout << "New literal: " << mk_pp (new_lit, m) << "\n";
                      );
            }
        }

        void substitute (expr_ref& fml, app_ref_vector& lits, expr_map& map) {
            expr_substitution sub (m);
            // literals
            for (unsigned i = 0; i < lits.size (); i++) {
                expr* new_lit = 0; proof* pr = 0;
                app* old_lit = lits.get (i);
                map.get (old_lit, new_lit, pr);
                if (new_lit) {
                    sub.insert (old_lit, new_lit);
                    TRACE ("qe",
                            tout << "old lit " << mk_pp (old_lit, m) << "\n";
                            tout << "new lit " << mk_pp (new_lit, m) << "\n";
                          );
                }
            }
            // substitute for x, if any
            expr* x_term = 0; proof* pr = 0;
            map.get (m_var->x (), x_term, pr);
            if (x_term) {
                sub.insert (m_var->x (), x_term);
                TRACE ("qe",
                        tout << "substituting for x by " << mk_pp (x_term, m) << "\n";
                      );
            }
            scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer (m);
            rep->set_substitution (&sub);
            (*rep)(fml);
        }

    public:
        arith_project_util(ast_manager& m): 
            m(m), a(m), m_rw(m), m_lits (m), m_terms (m) {}

        expr_ref operator()(model& mdl, app_ref_vector& vars, expr_ref_vector const& lits) {
            app_ref_vector new_vars(m);
            expr_ref_vector result(lits);
            for (unsigned i = 0; i < vars.size(); ++i) {
                app* v = vars.get (i);
                m_var = alloc(contains_app, m, v);
                try {
                    if (a.is_int (v)) {
                        IF_VERBOSE(1, verbose_stream() << "can't project int vars:" << mk_pp(v, m) << "\n";);
                        throw cant_project ();
                    }
                    project(mdl, result);
                    TRACE("qe", tout << "projected: " << mk_pp(v, m) << "\n";
                          for (unsigned i = 0; i < result.size(); ++i) {
                              tout << mk_pp(result.get (i), m) << "\n";
                          });
                }
                catch (cant_project) {
                    IF_VERBOSE(1, verbose_stream() << "can't project:" << mk_pp(v, m) << "\n";);
                    new_vars.push_back(v);
                }
            }
            vars.reset();
            vars.append(new_vars);
            return qe::mk_and(result);
        }

        void operator()(model& mdl, app_ref_vector& vars, expr_ref& fml) {
            app_ref_vector new_vars(m);
            app_ref_vector lits (m);
            expr_map map (m);
            for (unsigned i = 0; i < vars.size(); ++i) {
                app* v = vars.get (i);
                m_var = alloc(contains_app, m, v);
                try {
                    map.reset ();
                    lits.reset ();
                    if (a.is_int (v)) {
                        // factor out mod terms using div terms
                        expr_map mod_map (m);
                        mod2div (fml, mod_map);
                        TRACE ("qe",
                                tout << "factored out mod terms:" << "\n";
                                tout << mk_pp (fml, m) << "\n";
                              );
                    }
                    collect_lits (fml, lits);
                    app_ref div_lit (m);
                    project (mdl, lits, map, div_lit);
                    substitute (fml, lits, map);
                    if (div_lit) {
                        fml = m.mk_and (fml, div_lit);
                    }
                    TRACE("qe",
                            tout << "projected: " << mk_pp(v, m) << " "
                                 << mk_pp(fml, m) << "\n";
                         );
                    DEBUG_CODE(
                        expr_ref bval (m);
                        SASSERT (mdl.eval (fml, bval, true) && m.is_true (bval));
                    );
                }
                catch (cant_project) {
                    IF_VERBOSE(1, verbose_stream() << "can't project:" << mk_pp(v, m) << "\n";);
                    new_vars.push_back(v);
                }
            }
            vars.reset();
            vars.append(new_vars);
        }
    };

    expr_ref arith_project(model& mdl, app_ref_vector& vars, expr_ref_vector const& lits) {
        ast_manager& m = vars.get_manager();
        arith_project_util ap(m);
        return ap(mdl, vars, lits);
    }

    void arith_project(model& mdl, app_ref_vector& vars, expr_ref& fml) {
        ast_manager& m = vars.get_manager();
        arith_project_util ap(m);
        atom_set pos_lits, neg_lits;
        is_relevant_default is_relevant;
        mk_atom_default mk_atom;
        get_nnf (fml, is_relevant, mk_atom, pos_lits, neg_lits);
        ap(mdl, vars, fml);
    }
}
