#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <iostream>
#include <string>
#include <vector>
#include <set>
#include <boost/lexical_cast.hpp>
#include <boost/foreach.hpp>
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

  //-- options to be passed to Z3
  typedef std::pair<std::string,std::string> OptVal;
  std::set<OptVal> z3Opts;

  /*******************************************************************/
  //-- error handler
  /*******************************************************************/
  void pmuz_error_handler(Z3_context ctx, Z3_error_code ec)
  {
    std::cout << Z3_get_error_msg_ex (ctx, ec) << '\n';
  }
  
  /*******************************************************************/
  //-- print usage and exit
  /*******************************************************************/
  void usage(char *cmd)
  {
    std::cout << "Usage : " << cmd << " options\n";
    std::cout << "Options :\n";
    std::cout << "\t-dq             call query directly\n";
    std::cout << "\t-idl            datalog format input file (default: HORN)\n";
    std::cout << "\t-z3:x=y         option x=y to be passed to Z3\n";
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
      else if(strstr(argv[i],"-z3:") == argv[i]) {
        std::string optVal(argv[i]+4);
        size_t pos = optVal.find('=');
        if(pos == std::string::npos) {
          std::cerr << "ERROR: illegal Z3 option : " << argv[i] << '\n';
          usage(argv[0]);
        }
        std::string opt = optVal.substr(0,pos);
        std::string val = optVal.substr(pos+1);
        z3Opts.insert(OptVal(opt, val));        
      } else if(strstr(argv[i],".smt2") == argv[i] + (strlen(argv[i]) - 5)) {
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
  
  /*******************************************************************/
  //the parallel Mu-Z solver
  /*******************************************************************/
  class PMuz
  {
  private:
    //-- the Z3 context, fixedpoint object, and query
    Z3_context ctx;
    Z3_fixedpoint fxpt;
    Z3_ast query;

  public:
    //-- constructor
    PMuz() : ctx(0), fxpt(0), query(0) {}
    
    //-- initialize the solver
    void init()
    {
      //-- set parameters
      Z3_global_param_set("fixedpoint.engine", "spacer");
      BOOST_FOREACH(const OptVal &ov, z3Opts)
        Z3_global_param_set(ov.first.c_str(), ov.second.c_str());

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
    void destroy()
    {
      Z3_fixedpoint_dec_ref (ctx, fxpt);
      Z3_del_context (ctx);
    }

    //-- create the problem
    void createProblem()
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
          std::string rn = std::string("rule_") + boost::lexical_cast<std::string>(k); 
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
    void solve()
    {
      //-- call query directly
      if(directQuery) {
        Z3_lbool res = Z3_fixedpoint_query(ctx, fxpt, query);
        if(res == Z3_L_TRUE) std::cout << "VERIFICATION FAILED\n";
        else if(res == Z3_L_FALSE) std::cout << "VERIFICATION SUCCESSFUL\n";
        else std::cout << "VERIFICATION UNDEFINED\n";
      }
      //-- use exposed lowel-level IC3 API
      else {
        Z3_lbool res = Z3_fixedpoint_prepare_query(ctx, fxpt, query);

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
    }
  };
  
} //namespace pmuz

/*********************************************************************/
//-- the main file
/*********************************************************************/
int main(int argc, char *argv[])
{
  //-- parse options
  pmuz::parseOptions(argc, argv);

  //-- solve
  pmuz::PMuz pmuz;
  pmuz.init();
  pmuz.createProblem();
  pmuz.solve();
  pmuz.destroy();
}

/*********************************************************************/
//-- end of file
/*********************************************************************/
