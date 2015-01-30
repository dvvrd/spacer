#include <iostream>
extern "C" {
#include "z3.h"
}

int main(int argc, char *argv[])
{
  std::cout << "hello world ...\n";
  Z3_config config = Z3_mk_config ();
  Z3_context ctx = Z3_mk_context (config);
  Z3_del_config (config);
  Z3_fixedpoint fxpt = Z3_mk_fixedpoint (ctx);
  Z3_fixedpoint_inc_ref (ctx, fxpt);

  //-- get the fixedpoint parameter names from the description.
  Z3_param_descrs pardesc = Z3_fixedpoint_get_param_descrs(ctx,fxpt);
  Z3_string descStr = Z3_param_descrs_to_string(ctx,pardesc);
  //std::cout << descStr << '\n';

  //-- create fixedpoint parameters
  Z3_params params = Z3_mk_params(ctx);
  Z3_params_inc_ref(ctx,params);
  Z3_params_set_symbol(ctx,params, Z3_mk_string_symbol(ctx, "engine"), Z3_mk_string_symbol(ctx, "spacer"));
  //Z3_params_set_bool(ctx,params, Z3_mk_string_symbol(ctx,"bit_blast"), false);

  //-- validate parameters
  pardesc = Z3_fixedpoint_get_param_descrs(ctx,fxpt);
  Z3_params_validate(ctx,params,pardesc);
  
  //-- set fixedpoint parameters and free parameters
  Z3_fixedpoint_set_params(ctx,fxpt,params);
  Z3_params_dec_ref(ctx,params);

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
