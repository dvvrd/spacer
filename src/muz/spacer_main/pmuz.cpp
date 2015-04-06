/**
 * Copyright (c) 2014 Carnegie Mellon University. All Rights Reserved.

 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:

 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following acknowledgments
 * and disclaimers.

 * 2. Redistributions in binary form must reproduce the above
 * copyright notice, this list of conditions and the following
 * disclaimer in the documentation and/or other materials provided
 * with the distribution.

 * 3. The names "Carnegie Mellon University," "SEI" and/or "Software
 * Engineering Institute" shall not be used to endorse or promote
 * products derived from this software without prior written
 * permission. For written permission, please contact
 * permission@sei.cmu.edu.

 * 4. Products derived from this software may not be called "SEI" nor
 * may "SEI" appear in their names without prior written permission of
 * permission@sei.cmu.edu.

 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:

 * This material is based upon work funded and supported by the
 * Department of Defense under Contract No. FA8721-05-C-0003 with
 * Carnegie Mellon University for the operation of the Software
 * Engineering Institute, a federally funded research and development
 * center.

 * Any opinions, findings and conclusions or recommendations expressed
 * in this material are those of the author(s) and do not necessarily
 * reflect the views of the United States Department of Defense.

 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE
 * ENGINEERING INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS"
 * BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO WARRANTIES OF ANY KIND,
 * EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT
 * LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR MERCHANTABILITY,
 * EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL. CARNEGIE
 * MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.

 * This material has been approved for public release and unlimited
 * distribution.

 * DM-XXXXXXX
**/

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <iostream>
#include <string>
#include <vector>
#include <set>
#include <sstream>
#include "pmuz.h"
extern "C" {
#include "z3.h"
}

/*********************************************************************/
//-- options
/*********************************************************************/
namespace spacer
{


/*******************************************************************/
//-- error handler
/*******************************************************************/
void pmuz_error_handler(Z3_context ctx, Z3_error_code ec)
{
  std::cout << Z3_get_error_msg_ex (ctx, ec) << '\n';
}

//-- initialize the solver
void PMuz::init()
{
  //-- set parameters
  Z3_global_param_set("fixedpoint.engine", "spacer");

  //-- create context
  Z3_config config = Z3_mk_config ();
  ctx = Z3_mk_context (config);
  Z3_del_config (config);
  fxpt = Z3_mk_fixedpoint (ctx);
  Z3_fixedpoint_inc_ref (ctx, fxpt);

  //-- register error handler
  Z3_set_error_handler (ctx, pmuz_error_handler);
}

//-- destroy the solver
void PMuz::destroy()
{
  Z3_fixedpoint_dec_ref (ctx, fxpt);
  Z3_del_context (ctx);
}

//-- create the problem
void PMuz::createProblem()
{
  //-- if using datalog input
  if(inputDatalog) {
    Z3_ast_vector queries = Z3_fixedpoint_from_file (ctx, fxpt, inputFile.c_str());
    std::cout << "number of queries = " << Z3_ast_vector_size(ctx, queries) << '\n';
    query = Z3_ast_vector_get(ctx, queries, 0);
  }
  //-- if using HORN format
  else {
    //-- parse file to get list of assertions
    std::cout << "parsing HORN file " << inputFile << '\n';
    Z3_ast asserts = Z3_parse_smtlib2_file(ctx, inputFile.c_str(), 0, 0, 0, 0, 0, 0);
    //-- add rules and query
    Z3_app app = Z3_to_app(ctx, asserts);
    int nconjs = Z3_get_app_num_args(ctx, app);
    std::cout << "number of asserts = " << nconjs << '\n';

    //-- register relations
    for (int k = 0; k < nconjs-1; k++) {
      Z3_ast rule = Z3_get_app_arg(ctx, app, k);
      //-- non quantified formula
      if(Z3_is_app(ctx, rule)) {
        Z3_func_decl rule_fd = Z3_get_app_decl(ctx, Z3_to_app(ctx, rule));
        Z3_fixedpoint_register_relation(ctx, fxpt, rule_fd);
        continue;
      }
      //-- quantified formulas
      assert(Z3_is_quantifier_forall(ctx, rule));
      Z3_app qbody_app = Z3_to_app(ctx, Z3_get_quantifier_body(ctx, rule));
      Z3_func_decl qbody_fd = Z3_get_app_decl(ctx, qbody_app);
      assert(Z3_get_decl_kind(ctx, qbody_fd) == Z3_OP_IMPLIES);
      assert(Z3_get_app_num_args(ctx,qbody_app) == 2);
      Z3_ast head = Z3_get_app_arg(ctx, qbody_app, 1);
      assert(Z3_is_app(ctx, head));
      Z3_func_decl head_fd = Z3_get_app_decl(ctx, Z3_to_app(ctx, head));
      Z3_fixedpoint_register_relation(ctx, fxpt, head_fd);
    }

    //-- all but last assertion becomes rules
    for (int k = 0; k < nconjs-1; k++) {
      std::stringstream rnstr;
      rnstr << "rule_" << k;
      std::string rn(rnstr.str());
      Z3_symbol ruleName = Z3_mk_string_symbol(ctx, rn.c_str());
      Z3_fixedpoint_add_rule(ctx, fxpt, Z3_get_app_arg(ctx, app, k), ruleName);
    }
    //-- the last assertion must be of the form !q. and q becomes
    //-- the query
    Z3_app qapp = Z3_to_app(ctx, Z3_get_app_arg(ctx, app, nconjs-1));
    assert(Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, qapp)) == Z3_OP_NOT);
    assert(Z3_get_app_num_args(ctx, qapp) == 1);
    query = Z3_get_app_arg(ctx, qapp, 0);
  }
}

//-- solver the problem
Z3_lbool PMuz::solve()
{
  Z3_lbool res;
  //-- call query directly
  if(directQuery) {
    res = Z3_fixedpoint_query(ctx, fxpt, query);
    if(res == Z3_L_TRUE) std::cout << "VERIFICATION FAILED\n";
    else if(res == Z3_L_FALSE) std::cout << "VERIFICATION SUCCESSFUL\n";
    else std::cout << "VERIFICATION UNDEFINED\n";
  }
  //-- use exposed lowel-level IC3 API
  else {
#if WE_MERGE_ALL_SAGARS_CHANGES
    res = Z3_fixedpoint_prepare_query(ctx, fxpt, query);

    //-- if problem already solved when preparing
    if (res == Z3_L_FALSE) {
      std::cout << "problem solved by simplification ...\n";
      std::cout << "VERIFICATION FAILED\n";
    } else {
      //-- initialize search
      assert(Z3_fixedpoint_init_root(ctx, fxpt) == Z3_L_TRUE);

      //-- keep doing strengthen and propagate till solution
      for(;;) {
        //-- strengthen
        res = Z3_fixedpoint_check_reachability(ctx, fxpt);
        if(res == Z3_L_FALSE) {
          Z3_fixedpoint_process_result(ctx, fxpt);
          std::cout << "VERIFICATION FAILED\n";
          break;
        }

        //-- propagate
        res = Z3_fixedpoint_propagate(ctx, fxpt);
        if(res == Z3_L_FALSE) {
          Z3_fixedpoint_process_result(ctx, fxpt);
          std::cout << "VERIFICATION SUCCESSFUL\n";
          break;
        }

        //-- add a frame
        assert(Z3_fixedpoint_inc_level(ctx, fxpt) == Z3_L_TRUE);
      }
    }
#else
    throw "Not Implemented";
#endif
  }
  return res;
}

} //namespace pmuz


/*********************************************************************/
//-- end of file
/*********************************************************************/
