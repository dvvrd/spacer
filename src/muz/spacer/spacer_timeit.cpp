/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    timeit.h

Abstract:

    Support for timers.

Author:

    Nikolaj Bjorner (nbjorner) 2006-09-22

Modified by:
    
    Derrick Karimi 2015-03-25

Revision History:

--*/
#include<iostream>
#include"spacer_timeit.h"
#include"memory_manager.h"
#include"spacer_wall_stopwatch.h"
#include<iomanip>

namespace spacer {

struct spacer_timeit::imp {
    spacer_wall_stopwatch      m_watch;
    spacer_wall_stopwatch      *m_accumulated_time;
    char const *   m_msg;
    std::ostream & m_out;
    double         m_start_memory;
    
    imp(char const * msg, std::ostream & out, spacer_wall_stopwatch *accumulated_time):
        m_accumulated_time(accumulated_time),
        m_msg(msg), 
        m_out(out),
        m_start_memory(static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024)) {
        m_watch.start();
        if (m_accumulated_time) m_accumulated_time->start();
    }

    ~imp() {
        if (m_accumulated_time) m_accumulated_time->stop();
        m_watch.stop();
        double end_memory = static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024);
        m_out << "(" << m_msg << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() 
              << " :before-memory " << std::fixed << std::setprecision(2) << m_start_memory 
              << " :after-memory " << std::fixed << std::setprecision(2) << end_memory ;
        if (m_accumulated_time)
          m_out << " :accumulated-time " << std::fixed << std::setprecision(2) << m_accumulated_time->get_seconds();
        m_out << ")" << std::endl;
    }
};

spacer_timeit::spacer_timeit(bool enable, char const * msg, std::ostream & out, spacer_wall_stopwatch *accumulated_time) {
    if (enable)
        m_imp = alloc(imp, msg, out, accumulated_time);
    else
        m_imp = 0;
}
   
spacer_timeit::~spacer_timeit() {
    if (m_imp)
        dealloc(m_imp);
}

} //namespace spacer
