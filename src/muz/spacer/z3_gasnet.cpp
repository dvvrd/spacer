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
#include<sstream>
#if _TRACE
#include"md5.h"
#endif


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
scoped_hsl_lock::scoped_hsl_lock(gasnet_hsl_t *lock, const bool &hold) : 
  m_hold(hold), m_lock(lock)
{
  if (m_hold) gasnet_hsl_lock(m_lock);
}
scoped_hsl_lock::~scoped_hsl_lock()
{
  if (m_hold) gasnet_hsl_unlock(m_lock);
}

msg_rec::msg_rec(
    const void * const buffer, 
    const size_t &buffer_size, 
    const gasnet_handler_t &sender_node_index) :
    m_buffer(memory::allocate(buffer_size)),
  m_buffer_size(buffer_size),
  m_node_index(sender_node_index) 
{
  if (buffer) memcpy(m_buffer,buffer,buffer_size);
}

msg_rec::~msg_rec()
{
  memory::deallocate(m_buffer);
}

void context::register_queue_msg_handler()
{
  m_queue_msg_handler_index = register_handler(
      (handler_fn_t)queue_msg_handler);
#ifdef _TRACE
  m_queue_msg_response_handler_index = register_handler(
      (handler_fn_t)queue_msg_response_handler);
#endif
  m_queue_long_msg_handler_index = register_handler(
      (handler_fn_t)queue_long_msg_handler);

  Z3GASNET_INIT_VERBOSE(
      << "queue_msg_handler registered as index: "
      << (int) m_queue_msg_handler_index << "\n";);
}

void context::queue_msg_handler(gasnet_token_t token,
          void* buffer, size_t buffer_size, 
          gasnet_handlerarg_t sender_node_index)
{

    //We don't have a use case for sending ourselves messages at this time
    //but there is no reason we couldn't support this
    SASSERT(sender_node_index != gasnet_mynode());

    msg_rec *front = alloc( msg_rec, 
          buffer, buffer_size, sender_node_index);

    { 
      scoped_hsl_lock hsl_lock(&m_handler_lock, true);
      m_msg_queue.push(front);
    }

#ifdef _TRACE
    MD5 md5;
    std::string hash(md5.digestMemory((BYTE *) buffer, (int) buffer_size));
    STRACE("gas", Z3GASNET_TRACE_PREFIX 
        << "receive " << buffer_size
        << " bytes, from node: " << sender_node_index
        << ", md5: " << hash << "\n" ;);

    Z3GASNET_CHECKCALL(gasnet_AMReplyMedium0( token,
          m_queue_msg_response_handler_index, 
          const_cast<char *>(hash.c_str()), hash.size() + 1));
#endif
}

#ifdef _TRACE
void context::queue_msg_response_handler(gasnet_token_t token,
          void* buffer, size_t buffer_size, 
          gasnet_handlerarg_t sender_node_index)
{
  std::list<std::string>::iterator i = m_unack_messages.begin();
  std::list<std::string>::iterator end = m_unack_messages.end();
  std::string acked_msg((const char *)buffer, buffer_size -1);
  
  size_t osize = m_unack_messages.size();
  SASSERT(osize > 0);
  bool acked = false;
  while(i != end)
  {
    if (*i == acked_msg)
    {
      m_unack_messages.erase(i);
      acked = true;
      break;
    }
    i++;
  }
  
  STRACE("gas", Z3GASNET_TRACE_PREFIX 
      << "Acknowledged " << acked << " msg(s) recieved, with " 
      << m_unack_messages.size() << " msg(s) unacknowleged" << "\n" ;);

  if (!acked)
  {
    std::cerr << "Node " << (int) gasnet_mynode() 
      << ": Unable to recognize response message\n";

  }

}
#endif


uintptr_t context::get_shared_segment_start()
{
    return (uintptr_t) m_seginfo_table[gasnet_mynode()].addr ;
}

size_t context::get_shared_segment_size()
{
    return (uintptr_t) m_seginfo_table[gasnet_mynode()].size ;
}

uintptr_t context::get_shared_segment_end()
{
    return get_shared_segment_start() + get_shared_segment_size();
}

bool context::can_reserve_buffer(size_t size)
{
  return m_next_seg_loc + size <= get_shared_segment_end();
}

uintptr_t context::reserve_buffer(size_t size)
{
  if (!can_reserve_buffer(size))
  {
    std::cerr << "Rolling shared memory segment buffer\n";
    m_next_seg_loc = get_shared_segment_start();
  }

  if (!can_reserve_buffer(size))
  {
    throw default_exception("Shared memory segment is not large enough to handle the request");
  }

  uintptr_t buf = m_next_seg_loc;
  m_next_seg_loc += size;

  STRACE("gas", Z3GASNET_TRACE_PREFIX 
      << "reserved buffer: " << buf << ", size: " << size << "\n";);

  return buf;
}


void context::transmit_msg(gasnet_node_t node_index, const std::string &msg)
{
#ifdef _TRACE
    MD5 md5;
    std::string hash(md5.digestMemory((BYTE*) const_cast<char *>(msg.c_str()),msg.size()+1));
    {
      scoped_interrupt_holder lock(true);
      m_unack_messages.push_back(hash);
    }
    STRACE("gas", Z3GASNET_TRACE_PREFIX 
        << "transmit " << msg.size()+1 << " bytes to node: " << node_index 
        << ", md5: " << hash << "\n" ;);
#endif

    if (msg.size() + 1 <= gasnet_AMMaxMedium())
      Z3GASNET_CHECKCALL(gasnet_AMRequestMedium1(
            node_index, m_queue_msg_handler_index,
            const_cast<char*>(msg.c_str()), msg.size()+1, gasnet_mynode() ));
    else if (msg.size() + 1 <= gasnet_AMMaxLongRequest())
    {
      uintptr_t mybuffer[2] = {
        reserve_buffer(msg.size()+1),
        msg.size()+1};

      //copy message contents to the reserved buffer on the 
      //shared memory segment
      memcpy((void*)mybuffer[0],msg.c_str(),msg.size()+1);

      //send the remote node the location where they may write on
      //the our shared memory segment
      Z3GASNET_CHECKCALL(gasnet_AMRequestMedium0(
            node_index, m_queue_long_msg_handler_index,
            (void*) mybuffer, sizeof(mybuffer) ));

    //uintptr_t remote_addr = receive_node_malloc(msg.size()+1);

    //
    //SASSERT(m_seginfo_table.size() > node_index);
    //void *dst = m_seginfo_table[node_index].addr;
    //Z3GASNET_CHECKCALL(gasnet_AMRequestLong1(
    //      node_index, m_queue_msg_handler_index,
    //      const_cast<char*>(msg.c_str()), msg.size()+1, dst, gasnet_mynode() ));
    }
    else
    {
      std::stringstream emsg;
      emsg << "Message is " << msg.size()+1 << " bytes, max size is " << gasnet_AMMaxLongRequest() 
        << " bytes.";
      throw default_exception(emsg.str().c_str());
    }

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
    scoped_hsl_lock hsl_lock(&m_handler_lock, true);
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
        << " bytes from node: " << m->get_node_index() << " and contains " 
        << n-1 << " more messages\n" ;);
    SASSERT(m->get_buffer_size());
    SASSERT(m->get_buffer());

  //TODO Optimization - replace with .assign, should be more efficient
    next_message.assign((const char *) m->get_buffer(),m->get_buffer_size()-1);

    dealloc(m);
  }

  return n > 0;
}

/* dhk
gasnet_node_t context::get_rcv_node()
{
    gasnet_node_t mynode = gasnet_mynode();
    gasnet_node_t num_nodes = gasnet_nodes();
    gasnet_node_t receive_node = (mynode + 1) % num_nodes;
    return receive_node;
}
*/

void context::set_seginfo_table()
{
  m_seginfo_table.resize(gasnet_nodes());
  Z3GASNET_CHECKCALL(gasnet_getSegmentInfo(&m_seginfo_table.front(),gasnet_nodes()));


  //dhk
  // gasnet_seginfo_t &remote_segment = m_seginfo_table[get_rcv_node()];
//m_rcv_node_free_list.push_back(std::pair<uintptr_t,size_t>(
//      (uintptr_t) remote_segment.addr, remote_segment.size));
  m_next_seg_loc = get_shared_segment_start();

}
  
/*
void context::receive_node_free(uintptr_t remote_address, size_t numbytes)
{
  m_rcv_node_free_list.push_back(std::pair<uintptr_t, size_t>(
        remote_address, numbytes));
}

//dhk
uintptr_t context::receive_node_malloc(size_t size)
{
    free_list::iterator i = m_rcv_node_free_list.begin();
    free_list::iterator end = m_rcv_node_free_list.end();

    while (i != end)
    {
      std::pair<uintptr_t, size_t> &cur(*i);

      if (cur.second >= size)
      {
        std::pair<uintptr_t, size_t> allocation(
            cur.first,
            size);

        cur.first += size;
        cur.second -= size;

        SASSERT(cur.second > 0);
        break;
      }

      i++;
    }
}


#ifdef _TRACE
void free_list_to_stream(std::ostream &stream)
{
  free_list::iterator i = m_rcv_node_free_list.begin();
  free_list::iterator end = m_rcv_node_free_list.end();

  while (i != end)
  {
    stream << "[" << i->first << ", " << i->second << "]--";
    i++;
  }
}
#endif
*/

void context::queue_long_msg_handler(gasnet_token_t token,
            void* buffer, size_t buffer_size)
{
  SASSERT(buffer_size == sizeof(uintptr_t)*2);
  uintptr_t *remote_buffer = (uintptr_t*) buffer;
  uintptr_t remote_addr = remote_buffer[0];
  uintptr_t size = remote_buffer[1];

  gasnet_node_t srcindex;
  Z3GASNET_CHECKCALL(gasnet_AMGetMsgSource (token, &srcindex));

  msg_rec *front = alloc( msg_rec , NULL, size, srcindex);

  gasnet_get_bulk(front->m_buffer,srcindex,(void*)remote_addr,size);
  
#ifdef _TRACE
  MD5 md5;
  std::string hash(md5.digestMemory((BYTE*) front->m_buffer,size));

  STRACE("gas", Z3GASNET_TRACE_PREFIX 
      << "bulk get " << size
      << " bytes, from node: " << srcindex
      << ", md5: " << hash << "\n" ;);

  Z3GASNET_CHECKCALL(gasnet_AMReplyMedium0( token,
        m_queue_msg_response_handler_index, 
        const_cast<char *>(hash.c_str()), hash.size() + 1));
#endif

  { 
    scoped_hsl_lock hsl_lock(&m_handler_lock, true);
    m_msg_queue.push(front);
  }
}

std::vector<gasnet_handlerentry_t> context::m_handlertable;
msg_queue context::m_msg_queue;
gasnet_handler_t context::m_queue_msg_handler_index;
std::vector<gasnet_seginfo_t> context::m_seginfo_table;
#ifdef _TRACE
std::list<std::string> context::m_unack_messages;
gasnet_handler_t context::m_queue_msg_response_handler_index;
#endif
//dhk context::free_list context::m_rcv_node_free_list;
uintptr_t context::m_next_seg_loc;
gasnet_handler_t context::m_queue_long_msg_handler_index;
gasnet_hsl_t context::m_handler_lock = GASNET_HSL_INITIALIZER;

} /// end z3gasnet namespace
#endif



