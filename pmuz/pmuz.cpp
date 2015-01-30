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
  bool res = Z3_fixedpoint_query(ctx, fxpt, Z3_ast_vector_get(ctx, queries, 0));
  std::cout << "result = " << res << "\n";

  //-- cleanup
  Z3_fixedpoint_dec_ref (ctx, fxpt);
  Z3_del_context (ctx);
  std::cout << "done ...\n";
}
