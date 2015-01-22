/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_util.cpp

Abstract:

    Utility functions for PDR.

Author:

    Krystof Hoder (t-khoder) 2011-8-19.

Revision History:


Notes: 
    

--*/

#include <sstream>
#include "arith_simplifier_plugin.h"
#include "array_decl_plugin.h"
#include "ast_pp.h"
#include "basic_simplifier_plugin.h"
#include "bv_simplifier_plugin.h"
#include "bool_rewriter.h"
#include "dl_util.h"
#include "for_each_expr.h"
#include "smt_params.h"
#include "model.h"
#include "ref_vector.h"
#include "rewriter.h"
#include "rewriter_def.h"
#include "util.h"
#include "pdr_manager.h"
#include "pdr_util.h"
#include "arith_decl_plugin.h"
#include "expr_replacer.h"
#include "model_smt2_pp.h"
#include "poly_rewriter.h"
#include "poly_rewriter_def.h"
#include "arith_rewriter.h"
#include "scoped_proof.h"
#include "var_subst.h"
#include "expr_safe_replace.h"


#include "model_evaluator.h"

#include "datatype_decl_plugin.h"
#include "bv_decl_plugin.h"

namespace pdr {

    unsigned ceil_log2(unsigned u) {
        if (u == 0) { return 0; }
        unsigned pow2 = next_power_of_two(u);
        return get_num_1bits(pow2-1);
    }

    std::string pp_cube(const ptr_vector<expr>& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }

    std::string pp_cube(const expr_ref_vector& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }

    std::string pp_cube(const app_ref_vector& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }
    
    std::string pp_cube(const app_vector& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }

    std::string pp_cube(unsigned sz, app * const * lits, ast_manager& m) {
        return pp_cube(sz, reinterpret_cast<expr * const *>(lits), m);
    }

    std::string pp_cube(unsigned sz, expr * const * lits, ast_manager& m) {
        std::stringstream res;
        res << "(";
        expr * const * end = lits+sz;
        for (expr * const * it = lits; it!=end; it++) {
            res << mk_pp(*it, m);
            if (it+1!=end) {
                res << ", ";
            }
        }
        res << ")";
        return res.str();
    }

  
  select_reducer::select_reducer (ast_manager &manager, model_ref &model) :
    m(manager), m_au (m), m_mev (m), m_rw (m), 
    m_model (model), m_side (m), m_pinned (m) {} 
  
  void select_reducer::reset ()
  {
    m_side.reset ();
    m_pinned.reset ();
    m_cache.reset ();
  }
  
  void select_reducer::operator() (expr_ref &fml)
  {
    expr_ref_vector conjs (m);
    qe::flatten_and (fml, conjs);
    for (unsigned i = 0; i < conjs.size (); ++i)
      conjs[i] = reduce_expr (conjs [i].get ());
    
    conjs.append (m_side);
    m_side.reset ();
    fml = m.mk_and(conjs.size(), conjs.c_ptr());        
    m_rw (fml);
  }
  
  expr* select_reducer::reduce_expr (expr *lit)
  {
    if (!is_app (lit)) return lit;
    
    expr *r = NULL;
    if (m_cache.find (to_app (lit), r)) return r;
    
    ptr_vector<app> todo;
    todo.push_back (to_app (lit));
    
    while (!todo.empty ())
    {
      app *a = todo.back ();
      unsigned sz = todo.size ();
      expr_ref_vector args (m);
      bool dirty = false;
      
      for (unsigned i = 0; i < a->get_num_args (); ++i)
      {
        expr *arg = a->get_arg (i);
        expr *narg = NULL;
        
        if (!is_app (arg)) args.push_back (arg);
        else if (m_cache.find (to_app (arg), narg)) 
        { 
          args.push_back (narg);
          dirty |= (arg != narg);
        }
        else 
          todo.push_back (to_app (arg));
      }
      
      if (todo.size () > sz) continue;
      todo.pop_back ();
      
      if (dirty)
      {
        r = m.mk_app (a->get_decl (), args.size (), args.c_ptr ());
        m_pinned.push_back (r);
      }
      else r = a;
      
      if (m_au.is_select (r)) r = reduce_select (to_app(r));
      
      m_cache.insert (a, r);
    }
    
    SASSERT (r);
    return r;
  }
  
  bool select_reducer::is_equals (expr *e1, expr *e2)
  {
    if (e1 == e2) return true;
    expr_ref val1 (m), val2 (m);
    m_mev.eval (*m_model, e1, val1);
    m_mev.eval (*m_model, e2, val2);
    return val1 == val2;
  }
  
  expr *select_reducer::reduce_select (app *a)
  {
    if (!m_au.is_store (a->get_arg (0))) return a;
    
    SASSERT (a->get_num_args () == 2 && "Multi-dimensional arrays are not supported");
    expr* array = a->get_arg (0);
    expr *j = a->get_arg (1);
    
    while (m_au.is_store (array))
    {
      a = to_app (array);
      expr *idx = a->get_arg (1);
      expr_ref cond (m);
      
      if (is_equals (idx, j))
      {
        cond = m.mk_eq (idx, j);
        m_rw (cond);
        if (!m.is_true (cond)) m_side.push_back (cond);
        return a->get_arg (2);
      }
      else
      {
        cond = m.mk_not (m.mk_eq (idx, j));
        m_rw (cond);
        if (!m.is_true (cond)) m_side.push_back (cond);
        array = a->get_arg (0);
      }
    }
    
    expr* args[2] = {array, j};
    m_pinned.push_back (m_au.mk_select (2, args));
    return m_pinned.back ();
  }
  
  
  
    void reduce_disequalities(model& model, unsigned threshold, expr_ref& fml) {
        ast_manager& m = fml.get_manager();
        expr_ref_vector conjs(m);
        qe::flatten_and(fml, conjs);
        obj_map<expr, unsigned> diseqs;
        expr* n, *lhs, *rhs;
        for (unsigned i = 0; i < conjs.size(); ++i) {
            if (m.is_not(conjs[i].get(), n) &&
                m.is_eq(n, lhs, rhs)) {
                if (!m.is_value(rhs)) {
                    std::swap(lhs, rhs);
                }
                if (!m.is_value(rhs)) {
                    continue;
                }
                diseqs.insert_if_not_there2(lhs, 0)->get_data().m_value++;
            }
        }
        expr_substitution sub(m);

        unsigned orig_size = conjs.size();
        unsigned num_deleted = 0;
        expr_ref val(m), tmp(m);
        proof_ref pr(m);
        pr = m.mk_asserted(m.mk_true());
        obj_map<expr, unsigned>::iterator it  = diseqs.begin();
        obj_map<expr, unsigned>::iterator end = diseqs.end();
        for (; it != end; ++it) {
            if (it->m_value >= threshold) {
                model.eval(it->m_key, val);
                sub.insert(it->m_key, val, pr);
                conjs.push_back(m.mk_eq(it->m_key, val));
                num_deleted += it->m_value;
            }
        }
        if (orig_size < conjs.size()) {
            scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer(m);
            rep->set_substitution(&sub);
            for (unsigned i = 0; i < orig_size; ++i) {
                tmp = conjs[i].get();
                (*rep)(tmp);
                if (m.is_true(tmp)) {
                    conjs[i] = conjs.back();
                    SASSERT(orig_size <= conjs.size());
                    conjs.pop_back();
                    SASSERT(orig_size <= 1 + conjs.size());
                    if (i + 1 == orig_size) {
                        // no-op.
                    }
                    else if (orig_size <= conjs.size()) {
                        // no-op
                    }
                    else {
                        SASSERT(orig_size == 1 + conjs.size());
                        --orig_size;
                        --i;
                    }
                }
                else {
                    conjs[i] = tmp;
                }
            }            
            IF_VERBOSE(2, verbose_stream() << "Deleted " << num_deleted << " disequalities " << conjs.size() << " conjuncts\n";);
        }
        fml = m.mk_and(conjs.size(), conjs.c_ptr());        
    }

    class test_diff_logic {
        ast_manager& m;
        arith_util a;
        bv_util    bv;
        bool m_is_dl;
        bool m_test_for_utvpi;

        bool is_numeric(expr* e) const {
            if (a.is_numeral(e)) {
                return true;
            }
            expr* cond, *th, *el;
            if (m.is_ite(e, cond, th, el)) {
                return is_numeric(th) && is_numeric(el);
            }
            return false;
        }
        
        bool is_arith_expr(expr *e) const {
            return is_app(e) && a.get_family_id() == to_app(e)->get_family_id();
        }

        bool is_offset(expr* e) const {
            if (a.is_numeral(e)) {
                return true;
            }
            expr* cond, *th, *el, *e1, *e2;
            if (m.is_ite(e, cond, th, el)) {
                return is_offset(th) && is_offset(el);
            }
            // recognize offsets.
            if (a.is_add(e, e1, e2)) {
                if (is_numeric(e1)) {
                    return is_offset(e2);
                }
                if (is_numeric(e2)) {
                    return is_offset(e1);
                }
                return false;
            }
            if (m_test_for_utvpi) {
                if (a.is_mul(e, e1, e2)) {
                    if (is_minus_one(e1)) {
                        return is_offset(e2);
                    }
                    if (is_minus_one(e2)) {
                        return is_offset(e1);
                    }
                }
            }
            return !is_arith_expr(e);
        }

        bool is_minus_one(expr const * e) const { 
            rational r; return a.is_numeral(e, r) && r.is_minus_one(); 
        }

        bool test_ineq(expr* e) const {
            SASSERT(a.is_le(e) || a.is_ge(e) || m.is_eq(e));
            SASSERT(to_app(e)->get_num_args() == 2);
            expr * lhs = to_app(e)->get_arg(0);
            expr * rhs = to_app(e)->get_arg(1);
            if (is_offset(lhs) && is_offset(rhs)) 
                return true;    
            if (!is_numeric(rhs)) 
                std::swap(lhs, rhs);
            if (!is_numeric(rhs)) 
                return false;    
            // lhs can be 'x' or '(+ x (* -1 y))'
            if (is_offset(lhs))
                return true;
            expr* arg1, *arg2;
            if (!a.is_add(lhs, arg1, arg2)) 
                return false;    
            // x
            if (m_test_for_utvpi) {
                return is_offset(arg1) && is_offset(arg2);
            }
            if (is_arith_expr(arg1)) 
                std::swap(arg1, arg2);
            if (is_arith_expr(arg1))
                return false;
            // arg2: (* -1 y)
            expr* m1, *m2;
            if (!a.is_mul(arg2, m1, m2))
                return false;
            return is_minus_one(m1) && is_offset(m2);
        }

        bool test_eq(expr* e) const {
            expr* lhs, *rhs;
            VERIFY(m.is_eq(e, lhs, rhs));
            if (!a.is_int_real(lhs)) {
                return true;
            }
            if (a.is_numeral(lhs) || a.is_numeral(rhs)) {
                return test_ineq(e);
            }
            return 
                test_term(lhs) && 
                test_term(rhs) &&
                !a.is_mul(lhs) &&
                !a.is_mul(rhs);
        }

        bool test_term(expr* e) const {
            if (m.is_bool(e)) {
                return true;
            }
            if (a.is_numeral(e)) {
                return true;
            }
            if (is_offset(e)) {
                return true;
            }
            expr* lhs, *rhs;
            if (a.is_add(e, lhs, rhs)) {
                if (!a.is_numeral(lhs)) {
                    std::swap(lhs, rhs);
                }
                return a.is_numeral(lhs) && is_offset(rhs);
            }
            if (a.is_mul(e, lhs, rhs)) {
                return is_minus_one(lhs) || is_minus_one(rhs);
            }
            return false;
        }

        bool is_non_arith_or_basic(expr* e) {
            if (!is_app(e)) {
                return false;
            }
            family_id fid = to_app(e)->get_family_id();

            if (fid == null_family_id && 
                !m.is_bool(e) && 
                to_app(e)->get_num_args() > 0) {
                return true;
            }
            return 
                fid != m.get_basic_family_id() &&
                fid != null_family_id &&
                fid != a.get_family_id() &&
                fid != bv.get_family_id();
        }

    public:
        test_diff_logic(ast_manager& m): m(m), a(m), bv(m), m_is_dl(true), m_test_for_utvpi(false) {}
       
        void test_for_utvpi() { m_test_for_utvpi = true; }

        void operator()(expr* e) {
            if (!m_is_dl) {
                return;
            }
            if (a.is_le(e) || a.is_ge(e)) {
                m_is_dl = test_ineq(e);
            }
            else if (m.is_eq(e)) {
                m_is_dl = test_eq(e);
            }
            else if (is_non_arith_or_basic(e)) {
                m_is_dl = false;
            }
            else if (is_app(e)) {
                app* a = to_app(e);                
                for (unsigned i = 0; m_is_dl && i < a->get_num_args(); ++i) {
                    m_is_dl = test_term(a->get_arg(i));
                }
            }

            if (!m_is_dl) {
                char const* msg = "non-diff: ";
                if (m_test_for_utvpi) {
                    msg = "non-utvpi: ";
                }
                IF_VERBOSE(1, verbose_stream() << msg << mk_pp(e, m) << "\n";);
            }
        }

        bool is_dl() const { return m_is_dl; }
    };

    bool is_difference_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls) {
        test_diff_logic test(m);
        expr_fast_mark1 mark;
        for (unsigned i = 0; i < num_fmls; ++i) {
            quick_for_each_expr(test, mark, fmls[i]);
        } 
        return test.is_dl();
    }  

    bool is_utvpi_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls) {
        test_diff_logic test(m);
        test.test_for_utvpi();
        expr_fast_mark1 mark;
        for (unsigned i = 0; i < num_fmls; ++i) {
            quick_for_each_expr(test, mark, fmls[i]);
        } 
        return test.is_dl();
    }  

    class arith_normalizer : public poly_rewriter<arith_rewriter_core> {
        ast_manager& m;
        arith_util   m_util;
        enum op_kind { LE, GE, EQ };
    public:
        arith_normalizer(ast_manager& m, params_ref const& p = params_ref()): poly_rewriter<arith_rewriter_core>(m, p), m(m), m_util(m) {}
        
        br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
            br_status st = BR_FAILED;
            if (m.is_eq(f)) {
                SASSERT(num_args == 2); return mk_eq_core(args[0], args[1], result);
            }

            if (f->get_family_id() != get_fid()) {
                return st;
            }
            switch (f->get_decl_kind()) {
            case OP_NUM: st = BR_FAILED; break;
            case OP_IRRATIONAL_ALGEBRAIC_NUM: st = BR_FAILED; break;
            case OP_LE:  SASSERT(num_args == 2); st = mk_le_core(args[0], args[1], result); break;
            case OP_GE:  SASSERT(num_args == 2); st = mk_ge_core(args[0], args[1], result); break;
            case OP_LT:  SASSERT(num_args == 2); st = mk_lt_core(args[0], args[1], result); break;
            case OP_GT:  SASSERT(num_args == 2); st = mk_gt_core(args[0], args[1], result); break;
            default: st = BR_FAILED; break;
            }
            return st;
        }      

    private:
        
        br_status mk_eq_core(expr* arg1, expr* arg2, expr_ref& result) {
            return mk_le_ge_eq_core(arg1, arg2, EQ, result);
        }
        br_status mk_le_core(expr* arg1, expr* arg2, expr_ref& result) {
            return mk_le_ge_eq_core(arg1, arg2, LE, result);
        }
        br_status mk_ge_core(expr* arg1, expr* arg2, expr_ref& result) {
            return mk_le_ge_eq_core(arg1, arg2, GE, result);
        }
        br_status mk_lt_core(expr* arg1, expr* arg2, expr_ref& result) {
            result = m.mk_not(m_util.mk_ge(arg1, arg2));
            return BR_REWRITE2;
        }
        br_status mk_gt_core(expr* arg1, expr* arg2, expr_ref& result) {
            result = m.mk_not(m_util.mk_le(arg1, arg2));
            return BR_REWRITE2;
        }

        br_status mk_le_ge_eq_core(expr* arg1, expr* arg2, op_kind kind, expr_ref& result) {
            if (m_util.is_real(arg1)) {
                numeral g(0);
                get_coeffs(arg1, g);
                get_coeffs(arg2, g);
                if (!g.is_one() && !g.is_zero()) {
                    SASSERT(g.is_pos());
                    expr_ref new_arg1 = rdiv_polynomial(arg1, g);
                    expr_ref new_arg2 = rdiv_polynomial(arg2, g);
                    switch(kind) {
                    case LE: result = m_util.mk_le(new_arg1, new_arg2); return BR_DONE;
                    case GE: result = m_util.mk_ge(new_arg1, new_arg2); return BR_DONE;
                    case EQ: result = m_util.mk_eq(new_arg1, new_arg2); return BR_DONE;
                    }
                }
            }
            return BR_FAILED;
        }

        void update_coeff(numeral const& r, numeral& g) {
            if (g.is_zero() || abs(r) < g) {
                g = abs(r);
            }
        }        

        void get_coeffs(expr* e, numeral& g) {
            rational r;
            unsigned sz;
            expr* const* args = get_monomials(e, sz);
            for (unsigned i = 0; i < sz; ++i) {
                expr* arg = args[i];
                if (!m_util.is_numeral(arg, r)) {
                    get_power_product(arg, r);
                }
                update_coeff(r, g);
            }
        }

        expr_ref rdiv_polynomial(expr* e, numeral const& g) {
            rational r;
            SASSERT(g.is_pos());
            SASSERT(!g.is_one());
            expr_ref_vector monomes(m);
            unsigned sz;           
            expr* const* args = get_monomials(e, sz);
            for (unsigned i = 0; i < sz; ++i) {
                expr* arg = args[i];
                if (m_util.is_numeral(arg, r)) {
                    monomes.push_back(m_util.mk_numeral(r/g, false));
                }
                else {
                    expr* p = get_power_product(arg, r);
                    r /= g;
                    if (r.is_one()) {
                        monomes.push_back(p);
                    }
                    else {
                        monomes.push_back(m_util.mk_mul(m_util.mk_numeral(r, false), p));
                    }
                }
            }
            expr_ref result(m);
            mk_add(monomes.size(), monomes.c_ptr(), result);
            return result;
        }
                
    };
    

    struct arith_normalizer_cfg: public default_rewriter_cfg {
        arith_normalizer m_r;
        bool rewrite_patterns() const { return false; }
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            return m_r.mk_app_core(f, num, args, result);
        }
        arith_normalizer_cfg(ast_manager & m, params_ref const & p):m_r(m,p) {}        
    };

    class arith_normalizer_star : public rewriter_tpl<arith_normalizer_cfg> {
        arith_normalizer_cfg m_cfg;
    public:
        arith_normalizer_star(ast_manager & m, params_ref const & p):
            rewriter_tpl<arith_normalizer_cfg>(m, false, m_cfg),
            m_cfg(m, p) {}
    };


    void normalize_arithmetic(expr_ref& t) {
        ast_manager& m = t.get_manager();
        scoped_no_proof _sp(m);
        params_ref p;
        arith_normalizer_star rw(m, p);
        expr_ref tmp(m);
        rw(t, tmp);
        t = tmp;                
    }

    void replace_vars_by_consts (expr* fml, expr_ref& result, expr_ref_vector& consts, ast_manager& m) {
        // get free vars
        expr_free_vars vars;
        vars (fml);

        // mk substitution of vars by consts
        consts.reset ();
        unsigned num_vars = vars.size ();
        expr_safe_replace sub (m);
        for (unsigned i = 0; i < num_vars; i++) {
            sort* s = vars[i];
            if (!s) continue;
            // mk var
            var_ref v (m.mk_var (i, s), m);
            // mk const
            std::stringstream ss;
            ss << "v" << i;
            symbol sym (ss.str ().c_str ());
            app_ref c (m.mk_const (sym, s), m);
            // insert subst pair
            sub.insert (v, c);
            consts.push_back (c);
        }

        // substitute
        result = fml;
        sub (result);
    }
          
expr* apply_accessor(ast_manager &m,
                     ptr_vector<func_decl> const& acc,
                     unsigned j,
                     func_decl* f,
                     expr* c) {
  if (is_app(c) && to_app(c)->get_decl() == f) {
    return to_app(c)->get_arg(j);
  }
  else {
    return m.mk_app(acc[j], c);
  }
}

  void expand_literals(ast_manager &m, expr_ref_vector& conjs) {
    if (conjs.empty ()) return;
    arith_util arith(m);
    datatype_util dt(m);
    bv_util       bv(m);
    expr* e1, *e2, *c, *val;
    rational r;
    unsigned bv_size;

    TRACE("pdr", 
          tout << "begin expand\n";
          for (unsigned i = 0; i < conjs.size(); ++i) {
            tout << mk_pp(conjs[i].get(), m) << "\n";
          });

    for (unsigned i = 0; i < conjs.size(); ++i) {
      expr* e = conjs[i].get();
      if (m.is_eq(e, e1, e2) && arith.is_int_real(e1)) {
        conjs[i] = arith.mk_le(e1,e2);
        if (i+1 == conjs.size()) {
          conjs.push_back(arith.mk_ge(e1, e2));
        }
        else {
          conjs.push_back(conjs[i+1].get());
          conjs[i+1] = arith.mk_ge(e1, e2);
        }
        ++i;
      }
      else if ((m.is_eq(e, c, val) && is_app(val) && dt.is_constructor(to_app(val))) ||
               (m.is_eq(e, val, c) && is_app(val) && dt.is_constructor(to_app(val)))){
        func_decl* f = to_app(val)->get_decl();
        func_decl* r = dt.get_constructor_recognizer(f);
        conjs[i] = m.mk_app(r, c);
        ptr_vector<func_decl> const& acc = *dt.get_constructor_accessors(f);
        for (unsigned j = 0; j < acc.size(); ++j) {
          conjs.push_back(m.mk_eq(apply_accessor(m, acc, j, f, c), to_app(val)->get_arg(j)));
        }
      }
      else if ((m.is_eq(e, c, val) && bv.is_numeral(val, r, bv_size)) ||
               (m.is_eq(e, val, c) && bv.is_numeral(val, r, bv_size))) {
        rational two(2);
        for (unsigned j = 0; j < bv_size; ++j) {
          parameter p(j);
          //expr* e = m.mk_app(bv.get_family_id(), OP_BIT2BOOL, 1, &p, 1, &c);
          expr* e = m.mk_eq(m.mk_app(bv.get_family_id(), OP_BIT1), bv.mk_extract(j, j, c));
          if ((r % two).is_zero()) {
            e = m.mk_not(e);
          }
          r = div(r, two);
          if (j == 0) {
            conjs[i] = e;
          }
          else {
            conjs.push_back(e);
          }
        }
      }
    }
    TRACE("pdr", 
          tout << "end expand\n";
          for (unsigned i = 0; i < conjs.size(); ++i) {
            tout << mk_pp(conjs[i].get(), m) << "\n";
          });
  }
}

template class rewriter_tpl<pdr::arith_normalizer_cfg>;

