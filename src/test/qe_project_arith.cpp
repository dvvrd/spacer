#include "qe_project.h"
#include "qe.h"
#include "th_rewriter.h"
#include "smt2parser.h"
#include "arith_decl_plugin.h"
#include "reg_decl_plugins.h"
#include "arith_rewriter.h"
#include "ast_pp.h"
#include "qe_util.h"
#include "smt_context.h"
#include "expr_abstract.h"
#include "model_smt2_pp.h"

static expr_ref parse_fml(ast_manager& m, char const* str) {
    expr_ref result(m);
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    std::ostringstream buffer;
    buffer << "(declare-const x Real)\n"
           << "(declare-const y Real)\n"
           << "(declare-const z Real)\n"
           << "(declare-const u Real)\n"
           << "(declare-const v Real)\n"
           << "(declare-const t Real)\n"
           << "(declare-const a Real)\n"
           << "(declare-const b Real)\n"
           << "(declare-const b1 Bool)\n"
           << "(declare-const ix Int)\n"
           << "(declare-const iy Int)\n"
           << "(declare-const iz Int)\n"
           << "(assert " << str << ")\n";
    std::istringstream is(buffer.str());
    VERIFY(parse_smt2_commands(ctx, is));
    SASSERT(ctx.begin_assertions() != ctx.end_assertions());
    result = *ctx.begin_assertions();
    return result;
}

static char const* exampleb1 = "(and (= b1 true) (and (> x 0.0) (< y 2.0)))";
static char const* answerb1 = "(and b1 (< y 2.0))";

static char const* example1 = "(and (<= x 3.0) (<= (* 3.0 x) y) (<= z y))";
static char const* answer1 = "(<= z y)";

static char const* example2 = "(and (<= z x) (<= x 3.0) (<= (* 3.0 x) y) (<= z y))";
static char const* answer2 = "(and (<= z y) (<= z 3.0) (<= (* 3.0 z) y))";

static char const* example3 = "(and (<= z x) (<= x 3.0) (< (* 3.0 x) y) (<= z y))";
static char const* answer3 = "(and (<= z y) (<= z 3.0) (< (* 3.0 z) y))";

static char const* example4 = "(and (<= z x) (<= x 3.0) (not (>= (* 3.0 x) y)) (<= z y))";
static char const* answer4 = "(and (<= z y) (<= z 3.0) (< (* 3.0 z) y))";

static char const* example5 = "(and (<= y x) (<= z x) (<= x u) (<= x v) (<= x t))";
static char const* answer5 = "(and (<= y z) (<= z t) (<= z u) (<= z v))";

static char const* example6 = "(and (<= 0.0 (+ x z))\
     (>= y x) \
     (<= y x)\
     (<= (- u y) 0.0)\
     (>= x (+ v z))\
     (>= x 0.0)\
     (<= x 1.0))";
static char const* answer6 = "(and (<= y 1.0) (<= u y) (>= (+ y z) 0.0) (<= (+ v z) y) (<= 0 y))";

static char const* example7 = "(and (= y x) (<= z x) (<= x u) (<= x v) (<= x t))";
static char const* answer7 = "(and (<= z y) (<= y u) (<= y v) (<= y t))";

static char const* example8 = "(and (= x y) (< x 5.0))";
static char const* answer8 = "(< y 5.0)";

static char const* example9 = "(and (not (= x y)) (< x 5.0))";
static char const* answer9 = "true";

static char const* example10 = "(and (not (= x y)) (< x 5.0) (> x z) (> x 0.0))";
static char const* answer10 = "(and (<= z 0.0) (< 0.0 y))";

static char const* example11 = "(and (< 2.0 x) (<= 2.0 x) (> 10.0 x) (> 15.0 x))";
static char const* answer11 = "true";

static char const* example12 = "(or (< x 3.0) (= x 5.0))";
static char const* answer12 = "true";

static char const* example13 = "(not (and (< x 3.0) (= x 5.0)))";
static char const* answer13 = "true";

static char const* example14 = "(not (and (not (< x 3.0)) (not (= x 5.0))))";
static char const* answer14 = "true";

static char const* example15 = "(or (< x 3.0) (= x 5.0) (> x 10.0))";
static char const* answer15 = "true";

static char const* example16 = "(not (and (< x 3.0) (= x 5.0) (> x 10.0)))";
static char const* answer16 = "true";

static char const* example17 = "(not (and (not (< x 3.0)) (not (= x 5.0)) (not (> x 10.0))))";
static char const* answer17 = "true";

static char const* example18 = "(and (or (< x y) (< x z)) (> x 5.0) (> x 0.0) (> x 1.0)\
                                     (= y 5.0) (= z 6.0))";
static char const* answer18 = "(and (> z 5.0) (> z 0.0) (> z 1.0) (= y 5.0) (= z 6.0))";


// integer examples

static char const* example19 = "(and (< (- iy) (+ (* 3 ix) (* (- 2) iy) 1))\
                                     (< (- (* 2 ix) 6) iz)\
                                     (= (mod (+ ix 1) 2) 0))";
static char const* answer19 = "(and (< (* 2 iy) (+ 18 (* 3 iz)))\
                                    (= (mod (+ (* 2 iy) 6) 12) 0)\
                                    (= (mod (* 2 iy) 6) 0))";

static char const* example20 = "(= (* 2 ix) iy)";
static char const* answer20 = "(= (mod iy 2) 0)";

static char const* example21 = "(and (or (< ix 13) (< 15 ix)) (< ix iy))";
static char const* answer21 = "(< 16 iy)";

static char const* example22 = "(and (or (< (+ (* 3 ix) 1) 10) (> (- (* 7 ix) 6) 7))\
                                     (= (mod ix 2) 0))";
static char const* answer22 = "true";

static char const* example23 = "(and (< (* 2 ix) (+ iz 6))\
                                     (< (- iy 1) (* 3 ix))\
                                     (= (mod (+ (* 5 ix) 1) 4) 0))";
static char const* answer23 = "(and (< (* 10 iy) (* 15 (+ iz 6)))\
                                    (= (mod (* 10 iy) 30) 0)\
                                    (= (mod (+ (* 10 iy) 6) 24) 0))";

static char const* example24 = "(and (or (< ix 63) (< 39 ix))\
                                     (= (mod ix 42) 0)\
                                     (= (mod ix 21) 0))";
static char const* answer24 = "true";

static char const* example25 = "(and (<= (+ (* 3 iy) ix) 10) (<= 20 (- iy ix)))";
static char const* answer25 = "(and (<= ix (- 13)) (= (mod (+ 60 (* 3 ix)) 3) 0))";

static char const* example26 = "(and (= (+ (* 3 ix) (* 4 iy)) 18) (<= (- (* 5 ix) iy) 7))";
static char const* answer26 = "(and (>= iy 3) (= (mod (- 90 (* 20 iy)) 15) 0))";

static char const* example27 = "(and (<= (+ (* 3 ix) (* 2 iy)) 18)\
                                     (<= (* 3 iy) (* 4 ix))\
                                     (<= (* 3 ix) (+ (* 2 iy) 1)))";
static char const* answer27 = "(and (<= iy 4) (= (mod (* 9 iy) 12) 0))";

static char const* example28 = "(and (< (* 3 ix) (+ iy iz))\
                                     (< (* 2 iz) (* 5 ix))\
                                     (< (- iy iz) (* 7 ix))\
                                     (= (mod ix 10) 0))";
static char const* answer28 = "(and (< (* 21 (* 2 iz)) (- (* 35 (+ iy iz)) 1050))\
                                    (< (* 15 (- iy iz)) (- (* 35 (+ iy iz)) 1050))\
                                    (= (mod (- (* 35 (+ iy iz)) 1050) 1050) 0))";

static char const* example29 = "(and (= iy (mod ix 2)) (> iy 0))";
static char const* answer29 = "(and (= (mod (- 1 iy) 2) 0) (> iy 0) (< iy 2))";

static char const* example30 = "(and (>= ix 3) (= (mod (+ (* 4 ix) iy) 4) 0))";
static char const* answer30 = "(= (mod iy 4) 0)";

static void test(char const *ex, char const *ans, char const *var, bool is_real) {
    smt_params params;
    params.m_model = true;
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref fml = parse_fml(m, ex);
    app_ref_vector vars(m);
    expr_ref_vector lits(m);
    if (is_real)
        vars.push_back(m.mk_const(symbol(var), a.mk_real()));
    else
        vars.push_back(m.mk_const(symbol(var), a.mk_int()));
    qe::flatten_and(fml, lits);

    smt::context ctx(m, params);
    ctx.assert_expr(fml);
    lbool result = ctx.check();
    SASSERT(result == l_true);
    ref<model> md;
    ctx.get_model(md);    

    std::cout << "Input: " << mk_pp(fml, m) << "\n";
    std::cout << "Model:" << "\n";
    model_smt2_pp (std::cout, m, *md, 0);

    expr_ref pr (fml, m);
    qe::arith_project(*md, vars, pr);
    
    expr_ref fml_ans = parse_fml(m, ans);
    std::cout << "One possible expected answer: " << mk_pp (fml_ans, m) << "\n";
    std::cout << "Answer: " << mk_pp(pr, m) << "\n";

    // check if answer is the same as expected
    smt::context ctx1 (m, params);
    ctx1.assert_expr (m.mk_not (m.mk_eq (fml_ans, pr)));
    result = ctx1.check ();
    bool same = (result == l_false);
    std::cout << "Answer is the expected one: " << (same ? "true" : "false") << "\n";
    std::cout << "\n";
    
}

static void test2(char const *ex) {
    smt_params params;
    params.m_model = true;
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref fml = parse_fml(m, ex);
    app_ref_vector vars(m);
    expr_ref_vector lits(m);
    vars.push_back(m.mk_const(symbol("x"), a.mk_real()));
    vars.push_back(m.mk_const(symbol("y"), a.mk_real()));
    vars.push_back(m.mk_const(symbol("z"), a.mk_real()));
    qe::flatten_and(fml, lits);

    smt::context ctx(m, params);
    ctx.push();
    ctx.assert_expr(fml);
    lbool result = ctx.check();
    SASSERT(result == l_true);
    ref<model> md;
    ctx.get_model(md);  
    ctx.pop(1);
    
    std::cout << mk_pp(fml, m) << "\n";

    expr_ref pr2(m), fml2(m);
    expr_ref_vector bound(m);
    ptr_vector<sort> sorts;
    svector<symbol> names;
    for (unsigned i = 0; i < vars.size(); ++i) {
        bound.push_back(vars[i].get());
        names.push_back(vars[i]->get_decl()->get_name());
        sorts.push_back(m.get_sort(vars[i].get()));
    }
    expr_abstract(m, 0, bound.size(), bound.c_ptr(), fml, fml2);
    fml2 = m.mk_exists(bound.size(), sorts.c_ptr(), names.c_ptr(), fml2);
    qe::expr_quant_elim qe(m, params);
    expr_ref pr1 = qe::arith_project(*md, vars, lits);
    qe(m.mk_true(), fml2, pr2);
    std::cout << mk_pp(pr1, m) << "\n";
    std::cout << mk_pp(pr2, m) << "\n";

    expr_ref npr2(m);
    npr2 = m.mk_not(pr2);
    ctx.push();
    ctx.assert_expr(pr1);
    ctx.assert_expr(npr2);
    VERIFY(l_false == ctx.check());
    ctx.pop(1);
    
    std::cout << "\n";
    
}

void tst_qe_project_arith() {
    //test2(example6);
    //return;

    // rational
    test(example1, answer1, "x", true);
    test(example2, answer2, "x", true);
    test(example3, answer3, "x", true);
    test(example4, answer4, "x", true);
    test(example5, answer5, "x", true);
    test(example6, answer6, "x", true);
    test(example7, answer7, "x", true);
    test(example8, answer8, "x", true);
    test(example9, answer9, "x", true);
    test(example10, answer10, "x", true);
    test(example11, answer11, "x", true);
    test(example12, answer12, "x", true);
    test(example13, answer13, "x", true);
    test(example14, answer14, "x", true);
    test(example15, answer15, "x", true);
    test(example16, answer16, "x", true);
    test(example17, answer17, "x", true);
    test (exampleb1, answerb1, "x", true);
    test (example18, answer18, "x", true);

    // integer
    test (example19, answer19, "ix", false);
    test (example20, answer20, "ix", false);
    test (example21, answer21, "ix", false);
    test (example22, answer22, "ix", false);
    test (example23, answer23, "ix", false);
    test (example24, answer24, "ix", false);
    test (example25, answer25, "iy", false);
    test (example26, answer26, "ix", false);
    test (example27, answer27, "ix", false);
    test (example28, answer28, "ix", false);
    test (example29, answer29, "ix", false);
    test (example30, answer30, "ix", false);
}
