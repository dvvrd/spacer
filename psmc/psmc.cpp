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
  Z3_fixedpoint fpt = Z3_mk_fixedpoint (ctx);
  Z3_fixedpoint_inc_ref (ctx, fpt);
  //Z3_ast_vector queries = Z3_fixedpoint_from_file (ctx, fpt, argv[1]);
  //std::cout << "number of queries = " << Z3_ast_vector_size(ctx, queries) << '\n';
  Z3_fixedpoint_dec_ref (ctx, fpt);
  Z3_del_context (ctx);
  std::cout << "done ...\n";
}
