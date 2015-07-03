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
#ifndef __Z3_GASNET_H
#define __Z3_GASNET_H
#ifdef Z3GASNET
#pragma GCC system_header //disable some warnings
#include<gasnet.h>
#include<gasnet_tools.h>
#include"lbool.h"
#include"z3_exception.h"
#include<ostream>
#include<vector>
#include<queue>

// measures the time, data, and number of messages
#define Z3GASNET_PROFILING

#ifdef Z3GASNET_PROFILING
#include"spacer_wall_stopwatch.h"
#endif
#ifndef _NO_OMP_
#include<omp.h>
#endif


// gasnet documentation states that messages are sent best
// effort.  To check during software construction that messages
// arrive with the correct contents, use the following define
// Also now can be turned on and off by parameter gasnet.verify_msgs
#define Z3GASNET_TRUST_BUT_VERIFY

#ifdef Z3GASNET_TRUST_BUT_VERIFY
#include<list>
#endif

#include "fixedpoint_params.hpp"

#define Z3GASNET_INIT_VERBOSE_STREAM_NAME std::cout

#ifndef _NO_OMP_
#define Z3GASNET_TRACE_PREFIX tout << "node " << gasnet_mynode() << "/" << gasnet_nodes() << " (" << ::getpid() << ":" << omp_get_thread_num() << "): " << __FILE__ << "(" << __LINE__ <<"): " 
#else
#define Z3GASNET_TRACE_PREFIX tout << "node " << gasnet_mynode() << "/" << gasnet_nodes() << " (" << ::getpid() << "): " << __FILE__ << "(" << __LINE__ <<"): " 
#endif

#define Z3GASNET_VERBOSE_STREAM( stream, code ) do {stream << "node " << gasnet_mynode() << "/" << gasnet_nodes() << " (" << ::getpid() << "): " << __FILE__ << "(" << __LINE__ <<"): "  code ; stream.flush();} while (false)

// no-op on these messages, they are just used during construction
#define Z3GASNET_INIT_VERBOSE( code ) 

// when debugging things that occur before normal z3 tracing and verbose mechanims are initialized, you
// can uncomment the following
//#define Z3GASNET_INIT_VERBOSE( code ) Z3GASNET_VERBOSE_STREAM( Z3GASNET_INIT_VERBOSE_STREAM_NAME , code )


#define Z3GASNET_CHECKCALL(fncall) do {                              \
    int _retval;                                                     \
    if ((_retval = fncall) != GASNET_OK) {                           \
      fprintf(stderr, "ERROR calling: %s\n"                          \
                   " at: %s:%i\n"                                    \
                   " error: %s (%s)\n",                              \
              #fncall, __FILE__, __LINE__,                           \
              gasnet_ErrorName(_retval), gasnet_ErrorDesc(_retval)); \
      fflush(stderr);                                                \
      gasnet_exit(_retval);                                          \
    }                                                                \
  } while(0)


#define Z3GASNET_CALL(fncall) do {fncall;} while(false)

//TODO DHK - abstrace barrier definitions so generic z3 header doesn't know
//specifics of how barriers are used, but still ensures they are uniquely numbered
//and there arn't too many of them
#define Z3GASNET_BARRIER_LEVEL_SOLVED 1

//the define can be used for larger sections of code only
//applicable with proiling
#ifdef Z3GASNET_PROFILING
//this define can be used for  sections of code applicable
//only when profiling
#define Z3GASNET_PROFILING_CALL(code) code;
#else
#define Z3GASNET_PROFILING_CALL(code)
#endif


namespace z3gasnet
{

extern int contextsolved;

bool node_works_on_item(
    const size_t &node_index, const size_t &num_nodes, 
    const size_t &work_item_index);

// When z3 is called from the PSMC Mesos Scheduler, the node given
// an environment variable of PSMC_TASK_ID=1 shall be the master
// otherwise the gasnet's  node number 0 is master
bool node_is_master();


gasnet_handlerentry_t *get_handler_table();
int get_num_handler_table_entires();

// typedef for generic handler function pointer
typedef void (*handler_fn_t)();


// This function should be called at static initialization time, before 
// the main function which calls gasnet_attach
// It will return the index of the handler
gasnet_handler_t register_handler(handler_fn_t handler);

// This function will find a handler by its function pointer
// if it is found its index will be returned.  Valid index values
// for handlers are from [128..255] acording to gasnet docs.  If it is not
// found 0 will be returned, 0 should never be used as a user defined
// handler value
gasnet_handler_t  find_handler(handler_fn_t handler);

// for debugging purposes show information of the handler table
void handlertable_to_stream(std::ostream &strm);

// Will hold interrupts upon construction and resume them again
// when the object goes out of scope.  Occasionally you may 
// have client code that optinally wants to hold interrupts, for
// this situation you can pass false to the constructor and 
// the object then has no affect
struct scoped_interrupt_holder
{
  scoped_interrupt_holder(const bool &hold);
  ~scoped_interrupt_holder();
private:
  bool m_hold;
};

// when handler and client code share data structures
// this lock is used
struct scoped_hsl_lock
{
  scoped_hsl_lock(gasnet_hsl_t *lock, const bool &hold);
  ~scoped_hsl_lock();
private:
  bool m_hold;
  gasnet_hsl_t *m_lock;
};

// the message q is filled with local coppies of all
// messages.  medium messges are filled as they are
// recieved, in the message handler.  long messages are
// filled in the main thread as work is pulled off of
// the work queue
class msg_rec
{
  private:
    msg_rec(const msg_rec &rhs) {} //non copyable

  public:
    friend class context;

    msg_rec(
        const void * const buffer, 
        const size_t &buffer_size, 
        const gasnet_handler_t &sender_node_index);
    //msg_rec();
    ~msg_rec();

    const void * const get_buffer() const { return m_buffer; }
    size_t get_buffer_size() const { return m_buffer_size; }
    gasnet_node_t get_node_index() const { return m_node_index; }

  private:
    void *m_buffer;
    size_t m_buffer_size;
    gasnet_node_t m_node_index;
};

typedef std::queue<msg_rec*> msg_queue;

// the work item queue is filled in the long
// message handler, each item in the queue
// provides enough information for where to
// read on a remote node's shared segment
struct work_item
{
  uintptr_t addr;
  size_t size;
  gasnet_node_t node;
};
typedef std::queue<work_item*> work_queue;

#ifdef Z3GASNET_PROFILING
struct stats {
    unsigned pop_cnt;
    unsigned transmit_cnt;
    unsigned pop_bytes;
    unsigned transmit_bytes;
    spacer::spacer_wall_stopwatch pop_time;
    spacer::spacer_wall_stopwatch transmit_time;
    spacer::spacer_wall_stopwatch handler_time;
    spacer::spacer_wall_stopwatch total_time;
    stats() { reset(); }
    double sum_time() { return pop_time.get_seconds() + 
      transmit_time.get_seconds() + handler_time.get_seconds(); }
    unsigned sum_bytes() { return pop_bytes +  transmit_bytes; }
    void reset() { memset(this, 0, sizeof(*this)); }
};
#endif

//TODO think about moving everything aboce inside the context class,
//  except maybe the types and typedefs

class context
{
public:
  static std::vector<gasnet_handlerentry_t> &get_handlertable() {
    return context::m_handlertable; 
  }
  static void register_queue_msg_handlers();

  //sends a string message to the node at node_index
  static void transmit_msg(gasnet_node_t node_index, const std::string &msg);
  
  //removes the first message in this node's queue, and returns
  //false if there were no elements and next_message is unmodified
  //returns true and sets next_messsage to the message before popping
  //it from the queue
  static bool pop_front_msg(std::string& next_message);

  //set the information about the global address space, all of the shared
  //memory segments on all of the nodes
  static void set_seginfo_table();

  //TODO if any nodes are left in the queue, they will leak at exit
  //destroy static data
  //static void destroy();

#ifdef Z3GASNET_PROFILING      
  static void print_statistics(std::ostream &stat_stream);
#endif

  //typedef fixedpoint_params * params_ref_type1;
  //typedef fixedpoint_params const& params_ref_type;
  typedef void* params_ref_type;
  // stats are set when spacer_context is initialized
  static void set_params(params_ref_type  params);
  static const fixedpoint_params & get_params();

private:
  // the registered active messaging handlers
  static std::vector<gasnet_handlerentry_t> m_handlertable;

  // the representation of the global address space
  static std::vector<gasnet_seginfo_t> m_seginfo_table;
  
  // the following two queue's are shared between handler context
  // and client code and should be accessed via the handler lock
  static bool process_work_queue_item();
  static gasnet_hsl_t m_handler_lock;
  static work_queue m_work_queue;
  static msg_queue m_msg_queue;


  // handler for medium size instantaneous messages
  static void queue_msg_handler(gasnet_token_t token,
            void* buffer, size_t buffer_size);
  static gasnet_handler_t m_queue_msg_handler_index;

  // handler for long messages which are added to the work queue
  static void queue_long_msg_handler(gasnet_token_t token,
            void* buffer, size_t buffer_size);
  static gasnet_handler_t m_queue_long_msg_handler_index;

#ifdef Z3GASNET_TRUST_BUT_VERIFY
  // handler for verifying messages were delivered with the correct
  // contents
  static void queue_msg_response_handler(gasnet_token_t token,
            void* buffer, size_t buffer_size);
  static gasnet_handler_t m_queue_msg_response_handler_index;
  // remembers hashes of what messages were sent
  static std::list<std::string> m_unack_messages;
#endif

  // for reserving spots on the local node's shared segment
  static size_t get_shared_segment_size();
  static bool can_reserve_buffer(size_t size);
  static uintptr_t reserve_buffer(size_t size);
  static uintptr_t m_next_seg_loc;
  static uintptr_t get_shared_segment_start();
  static uintptr_t get_shared_segment_end();

#ifdef Z3GASNET_PROFILING      
  static stats m_stats;
#endif

  

  static params_ref_type m_params;

};

} //namesapce z3gasnet
#else

#define Z3GASNET_CHECKCALL(fncall)
#define Z3GASNET_CALL(fncall)

#endif

#endif

