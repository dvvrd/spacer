#include "ast.h"
#include "ast_pp.h"
#include "qe_array.h"
#include "reg_decl_plugins.h"
#include "smt2parser.h"
#include "scoped_proof.h"

// adapted from test/polynorm.cpp
static void parse_fml(ast_manager& m, std::string const& str, expr_ref& result) {
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true); // no check-sat, just parse
    std::istringstream is(str);
    VERIFY(parse_smt2_commands(ctx, is));
    SASSERT(ctx.begin_assertions() != ctx.end_assertions());
    result = *ctx.begin_assertions();
}

void test_qe (ast_manager& m, std::string const& str, qe_array& qea) {
    expr_ref fml (m);
    parse_fml (m, str, fml);

    std::cout << "QE input: " << mk_pp (fml, m) << "\n";
    expr_ref qf_fml (m);
    qea (fml.get (), qf_fml);
    std::cout << "QE output: " << mk_pp (qf_fml, m) << "\n";
}

void test_qe_var (ast_manager& m, std::string const& str, qe_array& qea) {
    expr_ref fml (m);
    parse_fml (m, str, fml);

    quantifier* qfml = to_quantifier (fml);
    unsigned num = qfml->get_num_decls ();

    expr_ref body (qfml->get_expr (), m);
    std::cout << "QE input: " << mk_pp (body, m) << "\n";
    uint_set var_idx; var_idx.insert (0);
    expr_ref qf_fml (body, m);
    qea (var_idx, qf_fml, num);
    std::cout << "QE output: " << mk_pp (qf_fml, m) << "\n";
}

void reset_ss (std::ostringstream& ss) {
    ss.str ("");
    ss.clear ();
}

void tst_qe_array () {
    ast_manager m;
    reg_decl_plugins (m);
    std::ostringstream fml_ss, ans_ss;
    qe_array qea (m);



    // selects



    // Exists (a, a[x]>y)
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const x Int)\n"
           << "(declare-const y Int)\n"
           << "(assert (exists ((a (Array Int Int))) (> (select a x) y)))\n";
    ans_ss << "(assert true)\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists (a, a[x]+a[x]>y)
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const x Int)\n"
           << "(declare-const y Int)\n"
           << "(assert (exists ((a (Array Int Int))) (> (+ (select a x) (select a x)) y)))\n";
    ans_ss << "(assert true)\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    //    
    //  Exists (a, a[0]==1 /\ a[39]==2 /\ b[0]==1 /\
    //              i>=n /\ 0<=k<n /\ a[k]!=0 /\ a[t0+t1k]==b[t0+t1k] /\
    //              (K 2)[t0+t1k]>0)
    //     
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const n Int)\n"
           << "(declare-const k Int)\n"
           << "(declare-const t0 Int)\n"
           << "(declare-const t1 Int)\n"
           << "(declare-const b (Array Int Int))\n"
           << "(assert (exists ((a (Array Int Int)))\n"
           << "                (and (= (select a 0) 1)\n"
           << "                     (= (select a 39) 2)\n"
           << "                     (= (select b 0) 1)\n"
           << "                     (>= i n)\n"
           << "                     (<= 0 k)\n"
           << "                     (< k n)\n"
           << "                     (not (= (select a k) 0))\n"
           << "                     (= (select a (+ t0 (* t1 k))) (select b (+ t0 (* t1 k))))\n"
           << "                     (> (select ((as const (Array Int Int)) 2) (+ t0 (* t1 k))) 0)\n"
           << "                     )))\n";
    ans_ss << "(declare-const i Int)\n"
           << "(declare-const n Int)\n"
           << "(declare-const k Int)\n"
           << "(declare-const t0 Int)\n"
           << "(declare-const t1 Int)\n"
           << "(declare-const b (Array Int Int))\n"
           << "(assert (exists ((a0 Int) (a39 Int) (ak Int) (aj Int))\n"
           << "                (and (= a0 1)\n"
           << "                     (= a39 2)\n"
           << "                     (= (select b 0) 1)\n"
           << "                     (>= i n)\n"
           << "                     (<= 0 k)\n"
           << "                     (< k n)\n"
           << "                     (not (= ak 0))\n"
           << "                     (= aj (select b (+ t0 (* t1 k))))\n"
           << "                     (=> (= k 0) (= ak a0))\n"
           << "                     (=> (= k 39) (= ak a39))\n"
           << "                     (=> (= (+ t0 (* t1 k)) 0) (= aj a0))\n"
           << "                     (=> (= (+ t0 (* t1 k)) 39) (= aj a39))\n"
           << "                     )))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // stores



    // Exists (a, a[i<-0][j] > 4)
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(assert (exists ((a (Array Int Int)))\n"
           << "                (> (select (store a i 0) j) 4)))\n";
    ans_ss << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(assert (not (= i j)))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists (a, a[i<-0] = b)
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const b (Array Int Int))\n"
           << "(assert (exists ((a (Array Int Int)))\n"
           << "                (= (store a i 0) b)))\n";
    ans_ss << "(declare-const i Int)\n"
           << "(declare-const b (Array Int Int))\n"
           << "(assert (= (select b i) 0))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists (a, a[i<-0] != b)
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const b (Array Int Int))\n"
           << "(assert (exists ((a (Array Int Int)))\n"
           << "                (not (= (store a i 0) b))))\n";
    ans_ss << "(assert true)\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists (a, a[i<-0][j<-1] [k] == l)
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(declare-const k Int)\n"
           << "(declare-const l Int)\n"
           << "(assert (exists ((a (Array Int Int)))\n"
           << "                (= (select\n"
           << "                         (store (store a i 0) j 1)\n"
           << "                         k) l)))\n";
    ans_ss << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(declare-const k Int)\n"
           << "(declare-const l Int)\n"
           << "(assert (and (=> (= k j) (= l 1))\n"
           << "             (=> (and (not (= k j)) (= k i)) (= l 0))))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists (a, b[a[i]<-2] == a[j<-0])
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(declare-const b (Array Int Int))\n"
           << "(assert (exists ((a (Array Int Int)))\n"
           << "                (= (store b (select a i) 2)\n"
           << "                   (store a j 0))))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists (a, a[i<-0] = a[j<-1])
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(assert (exists ((a (Array Int Int)))\n"
           << "                (= (store a i 0)\n"
           << "                   (store a j 1))))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists (a, b[i<-a][0] = a[j<-3])
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(declare-const b (Array Int (Array Int Int)))\n"
           << "(assert (exists ((a (Array Int Int)))\n"
           << "                (= (select (store b i a) 0)\n"
           << "                   (store a j 3))))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists (a, !a[i<-(b=c[0<-0])][j])
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(declare-const b (Array Int Int))\n"
           << "(declare-const c (Array Int Int))\n"
           << "(assert (exists ((a (Array Int Bool)))\n"
           << "                (not (select (store a i (= b (store c 0 0))) j))))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists (a, b[i<-a[j<-2]][0] = a[k<-3])
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(declare-const k Int)\n"
           << "(declare-const b (Array Int (Array Int Int)))\n"
           << "(assert (exists ((a (Array Int Int)))\n"
           << "                (= (select (store b i (store a j 2)) 0)\n"
           << "                   (store a j 3))))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists (a, b[i<-a[l<-5]][0] = a[a[j<-3][k]<-4])
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(declare-const k Int)\n"
           << "(declare-const l Int)\n"
           << "(declare-const b (Array Int (Array Int Int)))\n"
           << "(assert (exists ((a (Array Int Int)))\n"
           << "                (= (select (store b i (store a l 5)) 0)\n"
           << "                   (store a (select (store a j 3) k) 4))))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists (a, a[i<-c] != b)
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const c (Array Int Int))\n"
           << "(declare-const b (Array Int (Array Int Int)))\n"
           << "(assert (exists ((a (Array Int (Array Int Int))))\n"
           << "                (not (= (store a i c) b))))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";





    // eliminate multiple arrays



    // Exists ([a,i,b], b[i<-a[l<-5]][0] = a[a[j<-3][k]<-4])
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(declare-const k Int)\n"
           << "(declare-const l Int)\n"
           << "(assert (exists ((a (Array Int Int)) (i Int) (b (Array Int (Array Int Int))))\n"
           << "                (= (select (store b i (store a l 5)) 0)\n"
           << "                   (store a (select (store a j 3) k) 4))))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    // Exists ([a,b], And (a==b, c==a, c[2]>0, b==d, d[0]==a[5]))
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const c (Array Int Int))\n"
           << "(declare-const d (Array Int Int))\n"
           << "(assert (exists ((a (Array Int Int)) (b (Array Int Int)))\n"
           << "                (and (= a b)\n"
           << "                     (= c a)\n"
           << "                     (> (select c 2) 0)\n"
           << "                     (= b d)\n"
           << "                     (= (select d 0) (select a 5)))))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";



    //    
    //  Exists ([a,b], a[0]==1 /\ a[39]==2 /\ b[0]==1 /\
    //              i>=n /\ 0<=k<n /\ a[k]!=0 /\ a[t0+t1k]==b[t0+t1k] /\
    //              (K 2)[t0+t1k]>0)
    //     
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const i Int)\n"
           << "(declare-const n Int)\n"
           << "(declare-const k Int)\n"
           << "(declare-const t0 Int)\n"
           << "(declare-const t1 Int)\n"
           << "(assert (exists ((a (Array Int Int)) (b (Array Int Int)))\n"
           << "                (and (= (select a 0) 1)\n"
           << "                     (= (select a 39) 2)\n"
           << "                     (= (select b 0) 1)\n"
           << "                     (>= i n)\n"
           << "                     (<= 0 k)\n"
           << "                     (< k n)\n"
           << "                     (not (= (select a k) 0))\n"
           << "                     (= (select a (+ t0 (* t1 k))) (select b (+ t0 (* t1 k))))\n"
           << "                     (> (select ((as const (Array Int Int)) 2) (+ t0 (* t1 k))) 0)\n"
           << "                     )))\n";
    test_qe (m, fml_ss.str (), qea);
    std::cout << "\n\n";




    // the other operator()



    // Exists (a, a[x]>y)
    std::cout << "New Test" << "\n";
    reset_ss (fml_ss);
    reset_ss (ans_ss);
    fml_ss << "(declare-const x Int)\n"
           << "(declare-const y Int)\n"
           << "(assert (exists ((x Int) (y Int) (a (Array Int Int))) (> (select a x) y)))\n";
    ans_ss << "(assert true)\n";
    test_qe_var (m, fml_ss.str (), qea);
    std::cout << "\n\n";

}
