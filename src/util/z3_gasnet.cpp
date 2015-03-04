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

const gasnet_handlerarg_t handlerarg_flag_value = std::numeric_limits<gasnet_handlerarg_t>::min();

const int handler_contextsolve_index = 203;
const int replyhandler_contextsolve_index = 204;

typedef void (*handler_fn_t)();
gasnet_handlerentry_t htable[] = {
  { hidx_ping_shorthandler,  (handler_fn_t)ping_shorthandler  },
  { hidx_pong_shorthandler,  (handler_fn_t)pong_shorthandler  },
  { handler_contextsolve_index,  (handler_fn_t)handler_contextsolve  },
  { replyhandler_contextsolve_index,  (handler_fn_t)replyhandler_contextsolve  } 
};

gasnet_handlerentry_t *get_handler_table()
{
  return htable;
}
int get_num_handler_table_entires()
{
  return sizeof(htable)/sizeof(gasnet_handlerentry_t);
}

}

int ponghandeled = 0;


#endif



