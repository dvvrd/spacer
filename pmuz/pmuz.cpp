#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <iostream>
#include <string>
#include <vector>
#include <boost/lexical_cast.hpp>
extern "C" {
#include "z3.h"
}

/*********************************************************************/
//-- options
/*********************************************************************/
namespace pmuz
{
  //-- input file
  std::string inputFile;

  //-- is input file in DATALOG format
  bool inputDatalog = false;
  
  //-- whether to use query directly
  bool directQuery = false;

  /*******************************************************************/
  //-- print usage and exit
  /*******************************************************************/
  void usage(char *cmd)
  {
    std::cout << "Usage : " << cmd << " options\n";
    std::cout << "Options :\n";
    std::cout << "\t-dq             call query directly\n";
    std::cout << "\t-idl            datalog format input file\n";
    std::cout << "\tfoo.smt2        input file name\n";
    ::exit(30);
  }

  /*******************************************************************/
  //-- parse command line options
  /*******************************************************************/
  void parseOptions(int argc, char *argv[])
  {
    //-- print options for reproducibility
    std::cout << "CommandLine:";
    for(int i = 0;i < argc;++i) std::cout << ' ' << argv[i];
    std::cout << '\n';

    //-- parse options
    for(int i = 1;i < argc;++i) {
      if(!strcmp(argv[i],"-dq")) directQuery = true;
      else if(!strcmp(argv[i],"-idl")) inputDatalog = true;
      else if(strstr(argv[i],".smt2") == argv[i] + (strlen(argv[i]) - 5)) {
        if(!inputFile.empty()) {
          std::cerr << "ERROR: multiple inputs files : " << inputFile << ' ' << argv[i] << '\n';
          usage(argv[0]);
        } else inputFile = std::string(argv[i]);
      } else {
        std::cerr << "ERROR: illegal argument : " << argv[i] << '\n';
        usage(argv[0]);
      }
    }
  }
  
} //namespace pmuz

/*********************************************************************/
//-- the main file
/*********************************************************************/
int main(int argc, char *argv[])
{
  //-- parse options
  pmuz::parseOptions(argc, argv);
  
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
  Z3_ast_vector queries = Z3_fixedpoint_from_file (ctx, fxpt, pmuz::inputFile.c_str());
  std::cout << "number of queries = " << Z3_ast_vector_size(ctx, queries) << '\n';

  //-- solve the problem
  Z3_ast query = Z3_ast_vector_get(ctx, queries, 0);

  //-- call query directly
  if(pmuz::directQuery) {
    Z3_lbool res = Z3_fixedpoint_query(ctx, fxpt, query);
    std::cout << "result = " << res << "\n";
  }
  //-- use exposed lowel-level IC3 API
  else {
    Z3_lbool res = Z3_fixedpoint_prepare_query(ctx, fxpt, query);

    //-- if problem already solved when preparing
    if (res == Z3_L_FALSE) {
      std::cout << "problem solved by simplification ...\n";
      std::cout << "result = " << res << "\n";
    } else {
      //-- initialize search
      assert(Z3_fixedpoint_init_root(ctx, fxpt) == Z3_L_TRUE);

      //-- keep doing strengthen and propagate till solution
      for(;;) {
        //-- strengthen
        res = Z3_fixedpoint_check_reachability(ctx, fxpt);
        if(res == Z3_L_FALSE) {
          std::cout << "VERIFICATION FAILED\n";
          break;
        }

        //-- propagate
        res = Z3_fixedpoint_propagate(ctx, fxpt);
        if(res == Z3_L_FALSE) {
          std::cout << "VERIFICATION SUCCESSFUL\n";
          break;
        }

        //-- add a frame
        assert(Z3_fixedpoint_inc_level(ctx, fxpt) == Z3_L_TRUE);
      }
    }
  }

  //-- cleanup
  Z3_fixedpoint_dec_ref (ctx, fxpt);
  Z3_del_context (ctx);
}

/*********************************************************************/
//-- end of file
/*********************************************************************/
