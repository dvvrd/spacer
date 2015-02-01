#include <iostream>
extern "C" {
#include "z3.h"
}

int main(int argc, char *argv[])
{
  std::cout << "hello world ...\n";

  //-- set parameters
  Z3_global_param_set("verbose", "1");
  Z3_global_param_set("fixedpoint.engine", "spacer");

  //-- create context
  Z3_config config = Z3_mk_config ();
  Z3_context ctx = Z3_mk_context (config);
  Z3_del_config (config);
  Z3_fixedpoint fxpt = Z3_mk_fixedpoint (ctx);
  Z3_fixedpoint_inc_ref (ctx, fxpt);

  //-- load the problem from file
  Z3_ast_vector queries = Z3_fixedpoint_from_file (ctx, fxpt, argv[1]);
  std::cout << "number of queries = " << Z3_ast_vector_size(ctx, queries) << '\n';

  //-- solve the problem
  Z3_ast query = Z3_ast_vector_get(ctx, queries, 0);
  Z3_lbool res = Z3_fixedpoint_prepare_query(ctx, fxpt, query);

  //-- if problem already solved when preparing
  if (res == Z3_FALSE)
    std::cout << "result = " << res << "\n";
  else {
    res = Z3_fixedpoint_init_root(ctx, fxpt);
    std::cout << "result = " << res << "\n";
    res = Z3_fixedpoint_check_reachability(ctx, fxpt);
    std::cout << "result = " << res << "\n";
    res = Z3_fixedpoint_propagate(ctx, fxpt);
    std::cout << "result = " << res << "\n";
    res = Z3_fixedpoint_inc_level(ctx, fxpt);
    std::cout << "result = " << res << "\n";
  }

  //-- cleanup
  Z3_fixedpoint_dec_ref (ctx, fxpt);
  Z3_del_context (ctx);
  std::cout << "done ...\n";
}
