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

  expr_ref_vector mk_array_instantiation::getId(const expr_ref_vector& select_args, const app_ref& old_pred)
  {
    expr_ref_vector res(m);
    res.append(select_args.size()-1, select_args.c_ptr());
    return res;	
  }

  app_ref mk_array_instantiation::get_select(unsigned nb_indices, expr* const* args)
  {
     app_ref res(m);
     res=m_a.mk_select(nb_indices, args);
     return res;
  }

  app_ref mk_array_instantiation::get_new_predicate(const expr_ref_vector& indices, const app_ref& old_pred)
  {
    unsigned nb_old_args=old_pred->get_num_args();
    expr_ref_vector new_args(m);

    unsigned new_indices_pos=0;
    for(unsigned i=0;i<nb_old_args;i++)
    {
      expr*arg=old_pred->get_arg(i);
      if(m_a.is_array(get_sort(arg)))
      {
        unsigned nb_array_param=get_array_arity(get_sort(arg));
        unsigned nb_quantifiers=m_ctx.get_params().xform_instantiate_arrays_nb_per_type()+m_ctx.get_params().xform_instantiate_arrays_nb_per_array();
        for(unsigned j=0;j<nb_quantifiers;j++)
        {
          expr_ref_vector select_args(m);
          select_args.push_back(arg);
          for(unsigned k=0;k<nb_array_param;k++)
          {
            select_args.push_back(indices[new_indices_pos]);
            new_indices_pos++;
            
          }
          expr_ref_vector id = getId(select_args, old_pred);
          for(unsigned k=0;k<id.size();k++)
            new_args.push_back(id[k].get());
          new_args.push_back(get_select(select_args.size(), select_args.c_ptr()));
        }
        if(!m_ctx.get_params().xform_instantiate_arrays_enforce())
          new_args.push_back(arg);
      }
      else
        new_args.push_back(arg);
    }
    
    sort_ref_vector new_sorts(m);
    for(unsigned i=0;i<new_args.size();i++)
      new_sorts.push_back(get_sort(new_args[i].get()));

    app_ref res(m);
    res = m.mk_app(m.mk_func_decl(old_pred->get_decl()->get_name(), new_sorts.size(), new_sorts.c_ptr(), old_pred->get_decl()->get_range()), new_args.size(), new_args.c_ptr());
    return res;
  }


}

