/**********************************************************************
Copyright (c) 2014 Carnegie Mellon University. All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following acknowledgments and
disclaimers.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

3. The names "Carnegie Mellon University," "SEI" and/or "Software
Engineering Institute" shall not be used to endorse or promote
products derived from this software without prior written
permission. For written permission, please contact
permission@sei.cmu.edu.

4. Products derived from this software may not be called "SEI" nor may
"SEI" appear in their names without prior written permission of
permission@sei.cmu.edu.

5. Redistributions of any form whatsoever must retain the following
acknowledgment:

This material is based upon work funded and supported by the
Department of Defense under Contract No. FA8721-05-C-0003 with
Carnegie Mellon University for the operation of the Software
Engineering Institute, a federally funded research and development
center.

Any opinions, findings and conclusions or recommendations expressed in
this material are those of the author(s) and do not necessarily
reflect the views of the United States Department of Defense.

NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEEAING
INSTITUTE MATEAIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR
IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF
FITNESS FOR PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS
OBTAINED FROM USE OF THE MATEAIAL. CARNEGIE MELLON UNIVERSITY DOES NOT
MAKE ANY WARRANTY OF ANY KIND WITH RESPECT TO FREEDOM FROM PATENT,
TRADEMARK, OR COPYAIGHT INFAINGEMENT.

This material has been approved for public release and unlimited
distribution.

DM-XXXXXXX
**********************************************************************/
#ifdef Z3GASNET

#include<iostream>
#include"z3_gasnet.h"
#include<vector>
#include<limits.h>


namespace z3gasnet
{

bool node_works_on_item(
    const size_t &node_index, const size_t &num_nodes,
    const size_t &work_item_index)
{
    if (!num_nodes) return false;
    size_t remainder = work_item_index % num_nodes;
    return node_index == remainder;
}

bool node_is_master()
{
  return !gasnet_mynode();
}


/*
void ping_shorthandler(gasnet_token_t token) {
  std::cout << "ping handled on node" << gasnet_mynode() << std::endl;
  Z3GASNET_CHECKCALL(gasnet_AMReplyShort0(token, hidx_pong_shorthandler)); 
  std::cout << "replied pong on node" << gasnet_mynode() << std::endl;
} 

int ponghandled = 0;
void pong_shorthandler(gasnet_token_t token) 
{
  std::cout << "pong handled on node " << gasnet_mynode() << std::endl;
  ponghandled++;
}
*/

typedef void (*handler_fn_t)();

gasnet_handlerentry_t *get_handler_table()
{
  return &(z3gasnet_context::get_handlertable()[0]);
}

int get_num_handler_table_entires()
{
  //client handlers are given indexes [128..255]
  SASSERT(z3gasnet_context::get_handlertable().size() < 255-128);
  return (int) z3gasnet_context::get_handlertable().size();
}

gasnet_handler_t find_handler(handler_fn_t handler)
{
  int tablesize = get_num_handler_table_entires();
  for (int i = 0; i < tablesize; i++)
  {
    if (z3gasnet_context::get_handlertable()[i].fnptr == handler)
    {
      return z3gasnet_context::get_handlertable()[i].index;
    }
  }
  return 0;
}

gasnet_handler_t register_handler(handler_fn_t handler)
{
  Z3GASNET_INIT_VERBOSE(<< "Registering handler: " << (void*)handler 
      << " in table: " << (void*) &z3gasnet_context::get_handlertable() << "\n";);

  // gasnet documentation states user based indexes from [128..255]
  gasnet_handler_t foundindex = find_handler(handler);
  if (foundindex)
  {
    Z3GASNET_INIT_VERBOSE(<< "handler: " << (void*)handler << 
        " was already registered at index: " << foundindex <<"\n";);
    return foundindex;
  }
  
  size_t index = 128 + z3gasnet_context::get_handlertable().size();
  SASSERT(index >=128 and index <=255);
  
  Z3GASNET_INIT_VERBOSE( << "adding handler: " << (void*)handler << 
      " at index: " << index <<"\n";);
  z3gasnet_context::get_handlertable().resize(z3gasnet_context::get_handlertable().size()+1);
  gasnet_handlerentry_t &he = z3gasnet_context::get_handlertable().back();
  //he.index = reinterpret_cast<gasnet_handler_t>(index);
  he.index = index;
  he.fnptr = handler;

  Z3GASNET_INIT_VERBOSE( << "added handler entry: { index=" 
      << (int) z3gasnet_context::get_handlertable().back().index << ", fnptr=" 
      << (void*) z3gasnet_context::get_handlertable().back().fnptr << " } at position: "
      << z3gasnet_context::get_handlertable().size() << "\n" ;);

  return he.index;
}

void handlertable_to_stream(std::ostream &strm)
{
  int numentries = get_num_handler_table_entires();
  
//Z3GASNET_INIT_VERBOSE( << "table: " << (void*) & z3gasnet_context::get_handlertable() 
//    << " has " <<  z3gasnet_context::get_handlertable().size() << " entries\n" ;);

  for (int i = 0; i < numentries; i++)
  {
    gasnet_handlerentry_t &he = z3gasnet_context::get_handlertable()[i];
    strm << (int) he.index << "\t:\t" << (void *) he.fnptr <<"\n";
  }
}

int ponghandeled = 0;

scoped_interrupt_holder::scoped_interrupt_holder(const bool &hold) : m_hold(hold)
{
  if (m_hold) gasnet_hold_interrupts();
}
scoped_interrupt_holder::~scoped_interrupt_holder()
{
  if (m_hold) gasnet_resume_interrupts();
}

std::vector<gasnet_handlerentry_t> z3gasnet_context::m_handlertable;

int z3gasnet_context::m_testval = 6;


} /// end z3gasnet namespace
#endif



