/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    main.cpp

Abstract:

    Z3 command line tool.

Author:

    Leonardo de Moura (leonardo) 2006-10-10.
    Nikolaj Bjorner   (nbjorner) 

Adopted by:
    
    Derrick Karimi 2015-03-13

Revision History:

--*/
#include<iostream>
#include"trace.h"
#include"version.h"
#include"timeout.h"
#include"z3_exception.h"
#include"error_codes.h"
#include"gparams.h"
#include"env_params.h"
#include"z3_gasnet.h"
#ifdef Z3GASNET_PROFILING
#include"spacer_wall_stopwatch.h"
#endif
#include<vector>

#ifdef Z3GASNET
//Have to include in main  here for access to message handlers
#include "spacer_context.h"
#include <iostream>
#include <ostream>
#endif

extern "C" {
#include "z3.h"
}

#include "pmuz.h"
#include "pmuz_globals.h"


typedef enum { IN_UNSPECIFIED, IN_SMTLIB, IN_SMTLIB_2, IN_DATALOG, IN_DIMACS, IN_WCNF, IN_OPB, IN_Z3_LOG } input_kind;

std::string         g_aux_input_file;
char const *        g_input_file          = 0;
bool                g_standard_input      = false;
input_kind          g_input_kind          = IN_UNSPECIFIED;
bool                g_display_statistics  = false;
bool                g_display_istatistics = false;
std::string         g_profiles;
char const *        g_profile_names[] = { "def","gpdr","ic3"};

void error(const char * msg) {
    std::cerr << "Error: " << msg << "\n";
    std::cerr << "For usage information: z3 -h\n";
    exit(ERR_CMD_LINE);
}

#define STRINGIZE(x) #x
#define STRINGIZE_VALUE_OF(x) STRINGIZE(x)

void display_usage() {
    std::cout << "Z3 [version " << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER;
    std::cout << " - ";
#ifdef _AMD64_
    std::cout << "64";
#else
    std::cout << "32";
#endif
    std::cout << " bit";
#ifdef Z3GITHASH
    std::cout << " - build hashcode " << STRINGIZE_VALUE_OF(Z3GITHASH);
#endif
    std::cout << "]. (C) Copyright 2006-2014 Microsoft Corp, (C) Copyright 2015 Software Engineering Institute - Carnegie Mellon University.\n";
#ifdef Z3GASNET
    std::cout << "Usage: pmuz JOB_SIZE [options] [-file:]file\n";
#else
    std::cout << "Usage: pmuz [options] [-file:]file\n";
#endif
    std::cout << "\nInput format:\n";
    std::cout << "  -smt        use parser for SMT input format.\n";
    std::cout << "  -smt2       use parser for SMT 2 input format.\n";
    std::cout << "  -dl         use parser for Datalog input format.\n";
    std::cout << "  -dimacs     use parser for DIMACS input format.\n";
    std::cout << "  -log        use parser for Z3 log input format.\n";
    std::cout << "  -in         read formula from standard input.\n";
    std::cout << "\nMiscellaneous:\n";
    std::cout << "  -h, -?      prints this message.\n";
    std::cout << "  -version    prints version number of Z3.\n";
    std::cout << "  -v:level    be verbose, where <level> is the verbosity level.\n";
    std::cout << "  -nw         disable warning messages.\n";
    std::cout << "  -p          display Z3 global (and module) parameters.\n";
    std::cout << "  -pd         display Z3 global (and module) parameter descriptions.\n";
    std::cout << "  -pm:name    display Z3 module ('name') parameters.\n";
    std::cout << "  -pp:name    display Z3 parameter description, if 'name' is not provided, then all module names are listed.\n";
#ifdef Z3GASNET
    std::cout << "  -profile:name0,name1,...    set predefined profiles of Z3 parameters.  If name list is provided its size should be N.  If no profile names are provided, a predefined set of profiles will be used.\n";
#else
    std::cout << "  -profile:name   set predefined profiles of Z3 parameters, if name is not provided 'def' will be used.\n";
#endif
    std::cout << "  --"      << "          all remaining arguments are assumed to be part of the input file name. This option allows Z3 to read files with strange names such as: -foo.smt2.\n";
    std::cout << "\nResources:\n";
    // timeout and memout are now available on Linux and OSX too.
    std::cout << "  -T:timeout  set the timeout (in seconds).\n";
    std::cout << "  -t:timeout  set the soft timeout (in milli seconds). It only kills the current query.\n";
    std::cout << "  -memory:Megabytes  set a limit for virtual memory consumption.\n";
    // 
    std::cout << "\nOutput:\n";
    std::cout << "  -st         display statistics.\n";
#if defined(Z3DEBUG) || defined(_TRACE)
    std::cout << "\nDebugging support:\n";
#endif
#ifdef _TRACE
    std::cout << "  -tr:tag     enable trace messages tagged with <tag>.\n";
#endif
#ifdef Z3DEBUG
    std::cout << "  -dbg:tag    enable assertions tagged with <tag>.\n";
#endif
    std::cout << "\nParameter setting:\n";
    std::cout << "Global and module parameters can be set in the command line.\n";
    std::cout << "  param_name=value              for setting global parameters.\n";
    std::cout << "  module_name.param_name=value  for setting module parameters.\n";
    std::cout << "Use 'z3 -p' for the complete list of global and module parameters.\n";
}
   
void parse_cmd_line_args(int argc, char ** argv) {
    int i = 1;
    char * eq_pos = 0;
    while (i < argc) {
        char * arg = argv[i];    

        if (arg[0] == '-' && arg[1] == '-' && arg[2] == 0) {
            // Little hack used to read files with strange names such as -foo.smt2
            // z3 -- -foo.smt2
            i++;
            g_aux_input_file = "";
            for (; i < argc; i++) {
                g_aux_input_file += argv[i];
                if (i < argc - 1)
                    g_aux_input_file += " ";
            }
            if (g_input_file) {
                warning_msg("input file was already specified.");
            }
            else {
                g_input_file = g_aux_input_file.c_str();
            }
            break;
        }
        
        if (arg[0] == '-' 
#ifdef _WINDOWS
            || arg[0] == '/'
#endif
            ) {
            char * opt_name = arg + 1;
            // allow names such as --help
            if (*opt_name == '-')
                opt_name++;
            char * opt_arg  = 0;
            char * colon    = strchr(arg, ':');
            if (colon) {
                opt_arg = colon + 1;
                *colon  = 0;
            }
            if (strcmp(opt_name, "h") == 0 || strcmp(opt_name, "?") == 0 || strcmp(opt_name, "help") == 0) {
                display_usage();
                exit(0);
            }
            if (strcmp(opt_name, "version") == 0) {
                std::cout << "Z3 version " << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER << "\n";
                exit(0);
            }
            else if (strcmp(opt_name, "smt") == 0) {
                g_input_kind = IN_SMTLIB;
            }
            else if (strcmp(opt_name, "smt2") == 0) {
                g_input_kind = IN_SMTLIB_2;
            }
            else if (strcmp(opt_name, "in") == 0) {
                g_standard_input = true;
            }
            else if (strcmp(opt_name, "dimacs") == 0) {
                g_input_kind = IN_DIMACS;
            }
            else if (strcmp(opt_name, "wcnf") == 0) {
                g_input_kind = IN_WCNF;
            }
            else if (strcmp(opt_name, "bpo") == 0) {
                g_input_kind = IN_OPB;
            }
            else if (strcmp(opt_name, "log") == 0) {
                g_input_kind = IN_Z3_LOG;
            }
            else if (strcmp(opt_name, "st") == 0) {
                g_display_statistics = true; 
            }
            else if (strcmp(opt_name, "ist") == 0) {
                g_display_istatistics = true; 
            }
            else if (strcmp(opt_name, "v") == 0) {
                if (!opt_arg)
                    error("option argument (-v:level) is missing.");
                long lvl = strtol(opt_arg, 0, 10);
                set_verbosity_level(lvl);
            }
            else if (strcmp(opt_name, "file") == 0) {
                g_input_file = opt_arg;
            }
            else if (strcmp(opt_name, "T") == 0) {
                if (!opt_arg)
                    error("option argument (-T:timeout) is missing.");
                long tm = strtol(opt_arg, 0, 10);
                set_timeout(tm * 1000);
            }
            else if (strcmp(opt_name, "t") == 0) {
                if (!opt_arg)
                    error("option argument (-t:timeout) is missing.");
                Z3_global_param_set("timeout", opt_arg);
            }
            else if (strcmp(opt_name, "nw") == 0) {
                enable_warning_messages(false);
            }
            else if (strcmp(opt_name, "p") == 0) {
                gparams::display(std::cout, 0, false, false);
                exit(0);
            }
            else if (strcmp(opt_name, "pd") == 0) {
                gparams::display(std::cout, 0, false, true);
                exit(0);
            }
            else if (strcmp(opt_name, "pm") == 0) {
                if (opt_arg) {
                    gparams::display_module(std::cout, opt_arg);
                }
                else {
                    gparams::display_modules(std::cout);
                    std::cout << "\nUse -pm:name to display all parameters available at module 'name'\n";
                }
                exit(0);
            }
            else if (strcmp(opt_name, "pp") == 0) {
                if (!opt_arg)
                    error("option argument (-pp:name) is missing.");
                gparams::display_parameter(std::cout, opt_arg);
                exit(0);
            }
#ifdef _TRACE
            else if (strcmp(opt_name, "tr") == 0) {
                if (!opt_arg)
                    error("option argument (-tr:tag) is missing.");
                enable_trace(opt_arg);
            }
#endif
#ifdef Z3DEBUG
            else if (strcmp(opt_name, "dbg") == 0) {
                if (!opt_arg)
                    error("option argument (-dbg:tag) is missing.");
                enable_debug(opt_arg);
            }
#endif
            else if (strcmp(opt_name, "memory") == 0) {
                if (!opt_arg)
                    error("option argument (-memory:val) is missing.");
                Z3_global_param_set("memory_max_size", opt_arg);
            }
            else if (strcmp(opt_name, "profile") == 0) {
                g_profiles=!opt_arg ? "def" : opt_arg;
            }
            else {
                std::cerr << "Error: invalid command line option: " << arg << "\n";
                std::cerr << "For usage information: z3 -h\n";
                exit(ERR_CMD_LINE);
            }
        }
        else if (argv[i][0] != '"' && (eq_pos = strchr(argv[i], '='))) {
            char * key   = argv[i];
            *eq_pos      = 0;
            char * value = eq_pos+1; 
            Z3_global_param_set(key, value);
        }
        else {
            if (g_input_file) {
                warning_msg("input file was already specified.");
            }
            else {
                g_input_file = arg;
            }
        }
        i++;
    }
}

char const * get_extension(char const * file_name) {
    if (file_name == 0)
        return 0;
    char const * last_dot = 0;
    for (;;) {
        char const * tmp = strchr(file_name, '.');
        if (tmp == 0) {
            return last_dot;
        }
        last_dot  = tmp + 1;
        file_name = last_dot;
    }
}

void profiles_string_to_vec(
    std::vector<std::string> &profile_vec,
    const std::string  &profiles_str)
{
  
  using namespace std;

  profile_vec.clear();
  size_t end = 0;
  size_t start = 0;
  const string delim(",");

  while ( end != string::npos)
  {
      end = profiles_str.find( delim, start);

      // If at end, use length=maxLength.  Else use length=end-start.
      profile_vec.push_back(profiles_str.substr( start,
                     (end == string::npos) ? string::npos : end - start));

      // If at end, use start=maxSize.  Else use start=end+delimiter.
      start = (   ( end > (string::npos - delim.size()) )
                ?  string::npos  :  end + delim.size());
  }
}

void set_profile_params(const std::string &profile)
{
#ifdef Z3GASNET
  STRACE("gas", Z3GASNET_TRACE_PREFIX
      << "profile set to: " << profile << "\n";);
  size_t ms = std::string().max_size();

  STRACE("gas", Z3GASNET_TRACE_PREFIX
      << "System Info:\n\tgasnet_AMMaxMedium(): " << gasnet_AMMaxMedium() << "\n"
      << "\tgasnet_AMMaxLongRequest(): " << gasnet_AMMaxLongRequest() << "\n"
      << "\tgasnet_AMMaxLongReply(): " << gasnet_AMMaxLongReply() << "\n" 
      << "\tgasnet_getMaxLocalSegmentSize(): " << gasnet_getMaxLocalSegmentSize() << "\n" 
      << "\tsizeof(gasnet_handlerarg_t): " << sizeof(gasnet_handlerarg_t) << "\n" 
      << "\tsizeof(uintptr_t): " << sizeof(uintptr_t) << "\n" 
      << "\tsizeof(size_t): " << sizeof(size_t) << "\n" 
      << "\tsizeof(void*): " << sizeof(void*) << "\n" 
      << "\tstd::string::max_size(): " << ms << "\n" 
      ;);
#endif

  if (profile == "def")
  {
    Z3_global_param_set("fixedpoint.use_heavy_mev","true");
    Z3_global_param_set("fixedpoint.reset_obligation_queue","false");
    Z3_global_param_set("fixedpoint.pdr.flexible_trace","true");
    Z3_global_param_set("fixedpoint.spacer.elim_aux","false");
    
  }
  else if (profile == "ic3")
  {
    Z3_global_param_set("fixedpoint.use_heavy_mev","true");
    Z3_global_param_set("fixedpoint.pdr.flexible_trace","true");
    Z3_global_param_set("fixedpoint.spacer.elim_aux","false");
  }
  else if (profile == "gpdr")
  {
    Z3_global_param_set("fixedpoint.use_heavy_mev","true");
    Z3_global_param_set("fixedpoint.spacer.elim_aux","false");
  }
  else 
  {
    std::cerr << "Unrecognized profile: " << profile << std::endl;
    throw z3_error(ERR_CMD_LINE);
  }
}

void set_profile(std::vector<std::string> profile_vec)
{
  SASSERT(profile_vec.size() > 0);

#ifdef Z3GASNET

  //the user should have specified either 1 profile, or exactly 
  //number of nodes profiles
  size_t stock_profiles = sizeof(g_profile_names) / sizeof(char const *);
  if (profile_vec.size() == 1)
  {
    SASSERT(profile_vec[0] == "def");
    profile_vec.clear();
    for (size_t i = 0; i < stock_profiles && i < gasnet_nodes(); i++)
      profile_vec.push_back(g_profile_names[i]);
    SASSERT(profile_vec[0] == "def");
  }
  
  if (profile_vec.size() > gasnet_nodes())
  {
    std::cerr << "Either 0, 1 or " << std::min<size_t>(gasnet_nodes(),stock_profiles)
      << " profiles should be specified\n";
    throw z3_error(ERR_CMD_LINE);
  }

  set_profile_params(profile_vec[gasnet_mynode()]);

#else

  set_profile_params(profile_vec[0]);

#endif

}

unsigned core_main(bool &repeat, unsigned restarts)
{
  using namespace spacer;

  repeat = false; 
  //-- solve
  spacer::PMuz pmuz(g_input_file);
  pmuz.init();
  pmuz.createProblem();
#ifdef Z3GASNET
  unsigned budget = 1;
  SASSERT( restarts >= 0 );
  while(restarts--) budget *= 2;
  pmuz_globals::m_globals.m_cur_budget = budget;
  STRACE("gas", Z3GASNET_TRACE_PREFIX 
      << "Setting global budget to: " << budget << "\n";);
#endif
  Z3_lbool solution = pmuz.solve();
  if (solution == Z3_L_TRUE)
  {
    std::cout << "sat\n";
  }
  else if (solution == Z3_L_FALSE)
  {
    std::cout << "unsat\n";
  }
  else if (pmuz_globals::m_globals.m_spacer_context_restart) {
#ifdef Z3GASNET
    STRACE("gas", Z3GASNET_TRACE_PREFIX 
        << "Main is restarting pmuz node\n";);

    repeat = true;
#endif
  }
  else 
  {
        std::cout << "unknown\n";
  }

  unsigned return_value = Z3_get_error_code(pmuz.getZ3Context());
  pmuz.destroy();
  return return_value;
}



// borrowed from 
// http://forums.codeguru.com/showthread.php?460071-ostream-bit-bucket
class null_out_buf : public std::streambuf {
public:
    virtual std::streamsize xsputn ( const char * s, std::streamsize n ) { return n; }
};

class null_out_stream : public std::ostream {
public:
    null_out_stream() : std::ostream(&buf) {}
private:
   null_out_buf buf;
};

std::ostream &get_default_verbose_stream()
{
  //In local spawning mode, it makes no sense to see mulitple verbose streams from
  //multiple processes because they are not synchronized
  //if not the master node 0, then set the null stream as default
  char *spawnfn = gasnet_getenv("GASNET_SPAWNFN");
  if (spawnfn && !strncmp("L",spawnfn,1) && gasnet_mynode()) 
  {
    static null_out_stream nullstream;
    return nullstream;
  }
  return std::cerr;
}

int main(int argc, char ** argv) {

    try{


        unsigned return_value = 0;
        //memory::initialize(0);
        //memory::exit_when_out_of_memory(true, "ERROR: out of memory");

#ifdef Z3GASNET

        //Register the messange handlers 
        z3gasnet::context::register_queue_msg_handlers();

        // gasnet places itself in front of any applicaiton cmdline handling
        // it will strip off the arguments it uses inside gasnet_init and 
        // the returned state of argc, argv can be used as normal by the the app
        Z3GASNET_CHECKCALL(gasnet_init(&argc, &argv));

        //control verbose output, so we can avoid forked processes outputting
        //to the same stream
        set_verbose_stream(get_default_verbose_stream());

        // gasnet will block here until all nodes of the job are attached
        Z3GASNET_CHECKCALL(gasnet_attach(
              z3gasnet::get_handler_table(),
              z3gasnet::get_num_handler_table_entires(),
              gasnet_getMaxLocalSegmentSize(),0));

        z3gasnet::context::set_seginfo_table();

#endif

        parse_cmd_line_args(argc, argv);
        if (g_profiles.size())
        {
          std::vector<std::string> profile_vec;
          profiles_string_to_vec(profile_vec, g_profiles);
          set_profile(profile_vec);
        }

        env_params::updt_params();

        bool repeat = false;
        unsigned restarts = 0;
        do { return_value = core_main(repeat,restarts++); } while (repeat);

        verbose_stream () << "BRUNCH_STAT node_restarts " << restarts << "\n";

#ifdef Z3GASNET
        STRACE("gas", Z3GASNET_TRACE_PREFIX 
            << "Ready to exit\n";);

        gasnet_barrier_notify(0,0);
        Z3GASNET_CHECKCALL(gasnet_barrier_wait(0,0));
        gasnet_exit(return_value);
#endif

        return return_value;
    }
    catch (z3_exception & ex) {
        // unhandled exception

        std::cerr << "ERROR: " << ex.msg() << "\n";
        if (ex.has_error_code()) {
            Z3GASNET_CALL(gasnet_exit(ex.error_code()));
            return ex.error_code();
        }
        else {
            Z3GASNET_CALL(gasnet_exit(ERR_INTERNAL_FATAL));
            return ERR_INTERNAL_FATAL;
        }
    }
}

