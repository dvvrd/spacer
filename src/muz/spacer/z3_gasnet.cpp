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
#include"memory_manager.h"
#include"trace.h"


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
  const char *taskid(std::getenv("PSMC_TASK_ID"));
  if (taskid)
  {
    return taskid[0] == '1' and taskid[1] == 0;
  }

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
  return &(context::get_handlertable()[0]);
}

int get_num_handler_table_entires()
{
  //client handlers are given indexes [128..255]
  SASSERT(context::get_handlertable().size() < 255-128);
  return (int) context::get_handlertable().size();
}

gasnet_handler_t find_handler(handler_fn_t handler)
{
  int tablesize = get_num_handler_table_entires();
  for (int i = 0; i < tablesize; i++)
  {
    if (context::get_handlertable()[i].fnptr == handler)
    {
      return context::get_handlertable()[i].index;
    }
  }
  return 0;
}

gasnet_handler_t register_handler(handler_fn_t handler)
{
  Z3GASNET_INIT_VERBOSE(<< "Registering handler: " << (void*)handler 
      << " in table: " << (void*) &context::get_handlertable() << "\n";);

  // gasnet documentation states user based indexes from [128..255]
  gasnet_handler_t foundindex = find_handler(handler);
  if (foundindex)
  {
    Z3GASNET_INIT_VERBOSE(<< "handler: " << (void*)handler << 
        " was already registered at index: " << foundindex <<"\n";);
    return foundindex;
  }
  
  size_t index = 128 + context::get_handlertable().size();
  SASSERT(index >=128 and index <=255);
  
  Z3GASNET_INIT_VERBOSE( << "adding handler: " << (void*)handler << 
      " at index: " << index <<"\n";);
  context::get_handlertable().resize(context::get_handlertable().size()+1);
  gasnet_handlerentry_t &he = context::get_handlertable().back();
  //he.index = reinterpret_cast<gasnet_handler_t>(index);
  he.index = index;
  he.fnptr = handler;

  Z3GASNET_INIT_VERBOSE( << "added handler entry: { index=" 
      << (int) context::get_handlertable().back().index << ", fnptr=" 
      << (void*) context::get_handlertable().back().fnptr << " } at position: "
      << context::get_handlertable().size() << "\n" ;);

  return he.index;
}

void handlertable_to_stream(std::ostream &strm)
{
  int numentries = get_num_handler_table_entires();
  
//Z3GASNET_INIT_VERBOSE( << "table: " << (void*) & context::get_handlertable() 
//    << " has " <<  context::get_handlertable().size() << " entries\n" ;);

  for (int i = 0; i < numentries; i++)
  {
    gasnet_handlerentry_t &he = context::get_handlertable()[i];
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

msg_rec::msg_rec(
    const void * const buffer, 
    const size_t &buffer_size, 
    const gasnet_handler_t &sender_node_index) :
    m_buffer(memory::allocate(buffer_size)),
  m_buffer_size(buffer_size),
  m_node_index(sender_node_index) 
{
  memcpy(m_buffer,buffer,buffer_size);
}

msg_rec::~msg_rec()
{
  memory::deallocate(m_buffer);
}

void context::register_queue_msg_handler()
{
  m_queue_msg_handler_index = register_handler(
      (handler_fn_t)queue_msg_handler);

  Z3GASNET_INIT_VERBOSE(
      << "queue_msg_handler registered as index: "
      << (int) m_queue_msg_handler_index << "\n";);
}

void context::queue_msg_handler(gasnet_token_t token,
          void* buffer, size_t buffer_size, 
          gasnet_handlerarg_t sender_node_index)
{
    STRACE("gas", Z3GASNET_TRACE_PREFIX 
        << "handling message of " << buffer_size 
        << " bytes, from node: " << sender_node_index << "\n" ;);

    //We don't have a use case for sending ourselves messages at this time
    //but there is no reason we couldn't support this
    SASSERT(sender_node_index != gasnet_mynode());

    m_msg_queue.push(alloc( msg_rec, 
          buffer, buffer_size, sender_node_index));
}

void context::transmit_msg(gasnet_node_t node_index, const std::string &msg)
{
    STRACE("gas", Z3GASNET_TRACE_PREFIX 
        << "sending " << msg.size()+1 << " bytes to node: " << node_index 
        << ", using handler: " << (int) m_queue_msg_handler_index << "\n" ;);
    Z3GASNET_CHECKCALL(gasnet_AMRequestMedium1(
          node_index, m_queue_msg_handler_index,
          const_cast<char*>(msg.c_str()), msg.size()+1, gasnet_mynode() ));
}
  
/*
const char * const context::get_front_msg(size_t &string_size)
{
  const msg_rec *m = NULL;
  {
    scoped_interrupt_holder interrupt_lock(true);
    m = m_msg_queue.front();
  }
  const void * const vb = m->get_buffer();
  string_size = m->get_buffer_size();

  return (const char * const) vb;
}
*/
  
bool context::pop_front_msg(std::string &next_message)
{
  // Poll GASNet to assure any pending message handlers get called
  Z3GASNET_CHECKCALL(gasnet_AMPoll());

  msg_rec *m = NULL;
  size_t n;
  {
    // use the scope lock to access the same data which is accessed
    // in the context of a message interrupt
    scoped_interrupt_holder interrupt_lock(true);
    n = m_msg_queue.size();
    if (n)
    {
        m = m_msg_queue.front();    
        m_msg_queue.pop();
    }
  }

  if (m)
  {
    STRACE("gas", Z3GASNET_TRACE_PREFIX 
        << "dequeued a msg of " << m->get_buffer_size()
        << " bytes and contains " << n-1 << " more messages\n" ;);

  //TODO Optimization - replace with .assign, should be more efficient
    next_message = std::string((char *) m->get_buffer(),m->get_buffer_size()-1);
    dealloc(m);
  }

  return n > 0;
}

std::vector<gasnet_handlerentry_t> context::m_handlertable;
msg_queue context::m_msg_queue;
gasnet_handler_t context::m_queue_msg_handler_index;


} /// end z3gasnet namespace
#endif



