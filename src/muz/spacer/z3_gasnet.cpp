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

//#ifdef Z3GASNET_TRUST_BUT_VERIFY
#include"md5.h"
//#endif


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

void context::register_queue_msg_handlers()
{
  m_queue_msg_handler_index = register_handler(
      (handler_fn_t)queue_msg_handler);
#ifdef Z3GASNET_TRUST_BUT_VERIFY
  // though this should be optinally done if gasnet_verify_msgs
  // parameter is set, this funciton is called from main before
  // spacer context has a chance to initialize m_params
  m_queue_msg_response_handler_index = register_handler(
      (handler_fn_t)queue_msg_response_handler);
#endif
  m_queue_long_msg_handler_index = register_handler(
      (handler_fn_t)queue_long_msg_handler);

  Z3GASNET_INIT_VERBOSE(
      << "queue_msg_handler registered as: "
      << (int) m_queue_msg_handler_index << "\n";);
}

void context::queue_msg_handler(gasnet_token_t token,
          void* buffer, size_t buffer_size)
{
#ifdef Z3GASNET_PROFILING
    m_stats.handler_time.start();
#endif

    gasnet_node_t sender_node_index;
    Z3GASNET_CHECKCALL(gasnet_AMGetMsgSource(token, &sender_node_index));

    msg_rec *front = alloc( msg_rec, 
          buffer, buffer_size, sender_node_index);

    { 
      scoped_hsl_lock hsl_lock(&m_handler_lock, true);
      m_msg_queue.push(front);
    }

#ifdef Z3GASNET_TRUST_BUT_VERIFY
    if (get_params().gasnet_verify_msgs())
    {
      MD5 md5;
      std::string hash(md5.digestMemory((BYTE *) buffer, (int) buffer_size));
      STRACE("gas", Z3GASNET_TRACE_PREFIX 
          << "receive " << buffer_size
          << " bytes, from node: " << sender_node_index
          << ", md5: " << hash << "\n" ;);

      Z3GASNET_CHECKCALL(gasnet_AMReplyMedium0( token,
            m_queue_msg_response_handler_index, 
            const_cast<char *>(hash.c_str()), hash.size() + 1));
    }
#endif
#ifdef Z3GASNET_PROFILING
    m_stats.handler_time.stop();
#endif
}

#ifdef Z3GASNET_TRUST_BUT_VERIFY
void context::queue_msg_response_handler(gasnet_token_t token,
          void* buffer, size_t buffer_size)
{
#ifdef Z3GASNET_PROFILING
    m_stats.handler_time.start();
#endif

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

  SASSERT(acked);

#ifdef Z3GASNET_PROFILING
    m_stats.handler_time.stop();
#endif
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
#ifdef Z3GASNET_PROFILING
    m_stats.transmit_cnt++;
    m_stats.transmit_time.start();
#endif

#ifdef Z3GASNET_TRUST_BUT_VERIFY
    if (get_params().gasnet_verify_msgs())
    {
      MD5 md5;
      std::string hash(md5.digestMemory((BYTE*) const_cast<char *>(msg.c_str()),msg.size()+1));
      {
        scoped_interrupt_holder lock(true);
        m_unack_messages.push_back(hash);
      }
      STRACE("gas", Z3GASNET_TRACE_PREFIX 
          << "transmit " << msg.size()+1 << " bytes to node: " << node_index 
          << ", md5: " << hash << "\n" ;);
    }
#endif

    // for messages that can fit in medium size payload, send them
    // instantly
    if (msg.size() + 1 <= gasnet_AMMaxMedium())
    {
#ifdef Z3GASNET_PROFILING
      m_stats.transmit_bytes+=msg.size()+1;
#endif
      Z3GASNET_CHECKCALL(gasnet_AMRequestMedium0(
            node_index, m_queue_msg_handler_index,
            const_cast<char*>(msg.c_str()), msg.size()+1 ));
    }
    else 
    {
      // for messages that are long
      // 1. reserve a spot on the local node's shared segment
      // 2. copy the message contents to that location
      // 3. send a message to the reciever wich includes the location
      //    of the reserved spot on the segment
      // 4. the remote node handler recieves the message and queues a pending
      //    read of the spot on this local node
      // 5. outside of the handler context the remote node will then perform
      //    the actual read operation of the specified spot on this local node's
      //    shared memory segment
      
      uintptr_t mybuffer[2] = {
        reserve_buffer(msg.size()+1),
        msg.size()+1};

      //copy message contents to the reserved buffer on the 
      //shared memory segment
      memcpy((void*)mybuffer[0],msg.c_str(),msg.size()+1);

#ifdef Z3GASNET_PROFILING
      m_stats.transmit_bytes+=sizeof(mybuffer);
#endif
      //send the remote node the location where they may write on
      //the our shared memory segment
      Z3GASNET_CHECKCALL(gasnet_AMRequestMedium0(
            node_index, m_queue_long_msg_handler_index,
            (void*) mybuffer, sizeof(mybuffer) ));

    }

#ifdef Z3GASNET_PROFILING
     m_stats.transmit_time.stop();
#endif
}
  
bool context::process_work_queue_item()
{
  gasnet_hsl_lock(&m_handler_lock);
  if (!m_work_queue.size())
  {
    gasnet_hsl_unlock(&m_handler_lock);
    return false;
  }
  work_item *item = m_work_queue.front();
  m_work_queue.pop();
  gasnet_hsl_unlock(&m_handler_lock);

  msg_rec *back = alloc( msg_rec , NULL, item->size, item->node);

  gasnet_get_bulk(back->m_buffer,item->node,(void*)item->addr,item->size);


#ifdef Z3GASNET_TRUST_BUT_VERIFY
  if (get_params().gasnet_verify_msgs())
  {
    MD5 md5;
    std::string hash(md5.digestMemory((BYTE*) back->m_buffer,item->size));

    STRACE("gas", Z3GASNET_TRACE_PREFIX 
        << "bulk get " << item->size
        << " bytes, from node: " << item->node
        << ", md5: " << hash << "\n" ;);

    Z3GASNET_CHECKCALL(gasnet_AMRequestMedium0( item->node,
          m_queue_msg_response_handler_index, 
          const_cast<char *>(hash.c_str()), hash.size() + 1));
  }
#endif

  dealloc(item);

  gasnet_hsl_lock(&m_handler_lock);
  m_msg_queue.push(back);
  bool ret = m_work_queue.size() > 0;
  gasnet_hsl_unlock(&m_handler_lock);
  return ret;
}

bool context::pop_front_msg(std::string &next_message)
{
#ifdef Z3GASNET_PROFILING
    m_stats.pop_time.start();
#endif

  // Poll GASNet to assure any pending message handlers get called
    STRACE("gas", Z3GASNET_TRACE_PREFIX 
        << "polling for messages from pop_front_msg\n" ;);
  Z3GASNET_CHECKCALL(gasnet_AMPoll());
  // perform one read from work q
  process_work_queue_item();

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

#ifdef Z3GASNET_PROFILING
    m_stats.pop_cnt++;
    m_stats.pop_bytes += m->get_buffer_size();
#endif

  //TODO DHK Optimization - see if client can use bytes directly to avoid copy
    next_message.assign((const char *) m->get_buffer(),m->get_buffer_size()-1);

    dealloc(m);
  }

#ifdef Z3GASNET_PROFILING
    m_stats.pop_time.stop();
#endif
  return n > 0;
}

void context::set_seginfo_table()
{
  m_seginfo_table.resize(gasnet_nodes());
  Z3GASNET_CHECKCALL(gasnet_getSegmentInfo(&m_seginfo_table.front(),gasnet_nodes()));

  m_next_seg_loc = get_shared_segment_start();
  
#ifdef Z3GASNET_PROFILING
  m_stats.total_time.start();
#endif

}
  
void context::queue_long_msg_handler(gasnet_token_t token,
            void* buffer, size_t buffer_size)
{
#ifdef Z3GASNET_PROFILING
    m_stats.handler_time.start();
#endif
  SASSERT(buffer_size == sizeof(uintptr_t)*2);
  uintptr_t *remote_buffer = (uintptr_t*) buffer;

  work_item *read = alloc(work_item);
  read->addr = remote_buffer[0];
  read->size = remote_buffer[1];
  Z3GASNET_CHECKCALL(gasnet_AMGetMsgSource (token, &read->node));

  {
    scoped_hsl_lock lock(&m_handler_lock,true);
    m_work_queue.push(read);
  }
#ifdef Z3GASNET_PROFILING
    m_stats.handler_time.stop();
#endif
}

#ifdef Z3GASNET_PROFILING
void context::print_statistics(std::ostream &stats_stream)
{
  //TODO DHK figure out what is up with z3 statistics handling
  stats &s = m_stats;
  double total_time = s.total_time.get_seconds();

    stats_stream 
      << "BRUNCH_STAT pop_cnt " << s.pop_cnt << "\n"
      << "BRUNCH_STAT pop_time " << s.pop_time.get_seconds() << "\n"
      << "BRUNCH_STAT pop_mbytes " << s.pop_bytes/1024.0/1024.0 << "\n"
      << "BRUNCH_STAT transmit_cnt " << s.transmit_cnt << "\n"
      << "BRUNCH_STAT transmit_time " << s.transmit_time.get_seconds() << "\n"
      << "BRUNCH_STAT transmit_mbytes " << s.transmit_bytes/1024.0/1024.0 << "\n"
      << "BRUNCH_STAT handler_time " << s.handler_time.get_seconds() << "\n"
      << "BRUNCH_STAT total_time " << total_time << "\n"
      << "BRUNCH_STAT comm_ohd " << s.sum_time() / total_time << "\n"
      << "BRUNCH_STAT thuput_mbps " << s.sum_bytes()/1024.0/1024.0/s.sum_time() << "\n";
    stats_stream.flush();
}
#endif

void context::set_params(context::params_ref_type  params){ m_params = params; }
const fixedpoint_params & context::get_params() { 
  return *((fixedpoint_params *) m_params); }

// instantiations for static members of context
std::vector<gasnet_handlerentry_t> context::m_handlertable;
msg_queue context::m_msg_queue;
gasnet_handler_t context::m_queue_msg_handler_index;
std::vector<gasnet_seginfo_t> context::m_seginfo_table;
#ifdef Z3GASNET_TRUST_BUT_VERIFY
std::list<std::string> context::m_unack_messages;
gasnet_handler_t context::m_queue_msg_response_handler_index;
#endif
uintptr_t context::m_next_seg_loc;
gasnet_handler_t context::m_queue_long_msg_handler_index;
gasnet_hsl_t context::m_handler_lock = GASNET_HSL_INITIALIZER;
work_queue context::m_work_queue;
#ifdef Z3GASNET_PROFILING
stats context::m_stats;
#endif
context::params_ref_type context::m_params = NULL;

} /// end z3gasnet namespace
#endif



