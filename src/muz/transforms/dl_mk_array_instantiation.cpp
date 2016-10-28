/*++

Module Name:

    dl_mk_array_instantiation.h

Abstract:

    Does array instantiation

Author:

    Julien Braine

Revision History:   

--*/


#include "dl_mk_array_instantiation.h"
#include "dl_context.h"
#include "pattern_inference.h"
#include "dl_context.h"
#include "expr_safe_replace.h"
#include "expr_abstract.h"
#include"fixedpoint_params.hpp"
#include <queue>

namespace datalog {

  mk_array_instantiation::mk_array_instantiation(
        context & ctx, unsigned priority):
        plugin(priority),
        m(ctx.get_manager()),
        m_ctx(ctx),
        m_a(m)
  {
  }
  
  rule_set * mk_array_instantiation::operator()(rule_set const & source)
  {
    std::cout<<"Array Instantiation called with parameters :"
             <<" enforce="<<m_ctx.get_params().xform_instantiate_arrays_enforce()
             <<" nb_per_type="<<m_ctx.get_params().xform_instantiate_arrays_nb_per_type()
             <<" nb_per_array="<<m_ctx.get_params().xform_instantiate_arrays_nb_per_array()
             <<" slice_technique="<<m_ctx.get_params().xform_instantiate_arrays_slice_technique()
             <<"\n";
    return NULL;
  }
}

