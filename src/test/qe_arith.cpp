#include "qe_arith.h"
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
static char const* answer5 = "(and (<= z y) (<= y t) (<= y u) (<= y v))";

static char const* example6 = "(and (<= 0 (+ x z))\
     (>= y x) \
     (<= y x)\
     (<= (- u y) 0.0)\
     (>= x (+ v z))\
     (>= x 0.0)\
     (<= x 1.0))";

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

static void test(char const *ex, char const *ans) {
    smt_params params;
    params.m_model = true;
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref fml = parse_fml(m, ex);
    app_ref_vector vars(m);
    expr_ref_vector lits(m);
    vars.push_back(m.mk_const(symbol("x"), a.mk_real()));
    qe::flatten_and(fml, lits);

    smt::context ctx(m, params);
    ctx.assert_expr(fml);
    lbool result = ctx.check();
    SASSERT(result == l_true);
    ref<model> md;
    ctx.get_model(md);    
    expr_ref pr (fml, m);
    qe::arith_project(*md, vars, pr);
    
    std::cout << "Input: " << mk_pp(fml, m) << "\n";
    std::cout << "Model:" << "\n";
    model_smt2_pp (std::cout, m, *md, 0);
    expr_ref fml_ans = parse_fml(m, ans);
    std::cout << "One possible expected answer: " << mk_pp (fml_ans, m) << "\n";
    std::cout << "Answer: " << mk_pp(pr, m) << "\n";
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

void tst_qe_arith() {
    //test2(example6);
    //return;
    test(example1, answer1);
    test(example2, answer2);
    test(example3, answer3);
    test(example4, answer4);
    test(example5, answer5);
    test(example7, answer7);
    test(example8, answer8);
    test(example9, answer9);
    test(example10, answer10);
    test(example11, answer11);
    test(example12, answer12);
    test(example13, answer13);
    test(example14, answer14);
    test(example15, answer15);
    test(example16, answer16);
    test(example17, answer17);
    test (exampleb1, answerb1);
}
