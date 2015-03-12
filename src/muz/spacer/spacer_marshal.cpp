#include "spacer_marshal.h"

#include <sstream>
#include "cmd_context.h"
#include "smt2parser.h"
#include "vector.h"
#include "ast_pp.h"

namespace spacer
{
  std::string marshal (expr_ref e, ast_manager &m)
  {
    std::stringstream ss;
    ss << "(assert " << mk_pp (e, m) << ")";
    return ss.str ();
  }
  
  expr_ref unmarshal (std::istream &is, ast_manager &m)
  {
    cmd_context ctx (false, &m);
    ctx.set_ignore_check (true);
    if (!parse_smt2_commands (ctx, is)) return expr_ref (0, m);
    
    ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
    ptr_vector<expr>::const_iterator end = ctx.end_assertions();
    unsigned size = static_cast<unsigned>(end - it);
    return expr_ref (m.mk_and (size, it), m);
  }
  
  expr_ref unmarshal (std::string s, ast_manager &m)
  {
    std::istringstream is(s);
    return unmarshal (is, m);
  }
}
