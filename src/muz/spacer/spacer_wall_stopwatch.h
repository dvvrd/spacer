/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    spacer_wall_stopwatch.h

Abstract:

    High resolution time keeping.z3-trace-8117 using a wall clock

Original Author:

    Christoph Wintersteiger (t-cwinte) 2008-12-24
    src/util/stopwatch.h

Adapted by:
    Derrick H. Karimi 2015-03-10

Revision History:

--*/

#ifndef _WALL_spacer_wall_stopwatch_H_
#define _WALL_spacer_wall_stopwatch_H_

#if defined(_WINDOWS) || defined(_CYGWIN)

// Does this redefinition work?
#define ARRAYSIZE_TEMP ARRAYSIZE
#undef ARRAYSIZE

#include <windows.h>

namespace spacer {
class spacer_wall_stopwatch
{
private:
    LARGE_INTEGER m_elapsed;
    LARGE_INTEGER m_last_start_time;
    LARGE_INTEGER m_last_stop_time;
    LARGE_INTEGER m_frequency;

public:
    spacer_wall_stopwatch() {
        QueryPerformanceFrequency(&m_frequency); 
        reset(); 
    }

    ~spacer_wall_stopwatch() {};

    void reset() { m_elapsed.QuadPart = 0; }
    
    void start() { 
        QueryPerformanceCounter(&m_last_start_time); 
    }
    
    void stop() { 
        QueryPerformanceCounter(&m_last_stop_time);
        m_elapsed.QuadPart += m_last_stop_time.QuadPart - m_last_start_time.QuadPart;
    }

    double get_seconds() const { 
        return static_cast<double>(m_elapsed.QuadPart / static_cast<double>(m_frequency.QuadPart)) ;
    }

    double get_current_seconds() const {
        LARGE_INTEGER t;
        QueryPerformanceCounter(&t);
        return static_cast<double>( (t.QuadPart - m_last_start_time.QuadPart) / static_cast<double>(m_frequency.QuadPart)); 
    }
};
}

#undef ARRAYSIZE
#define ARRAYSIZE ARRAYSIZE_TEMP
#undef max
#undef min


#elif defined(__APPLE__) && defined (__MACH__) // Mac OS X

#include<mach/mach.h>
#include<mach/clock.h>

namespace spacer {
class spacer_wall_stopwatch {
    unsigned long long m_time; // elapsed time in ns
    bool               m_running;
    clock_serv_t       m_host_clock;
    mach_timespec_t    m_start;
    
public:
    spacer_wall_stopwatch():m_time(0), m_running(false) {
        host_get_clock_service(mach_host_self(), SYSTEM_CLOCK, &m_host_clock);
    }

    ~spacer_wall_stopwatch() {}
    
    void reset() {
        m_time = 0ull;
    }
    
    void start() {
        if (!m_running) {
            clock_get_time(m_host_clock, &m_start);
            m_running = true;
        }
    }

    void stop() {
        if (m_running) {
            mach_timespec_t _stop;
            clock_get_time(m_host_clock, &_stop);
            m_time += (_stop.tv_sec - m_start.tv_sec) * 1000000000ull;
	    m_time += (_stop.tv_nsec - m_start.tv_nsec);
            m_running = false;
        }
    }

    double get_seconds() const { 
        if (m_running) {
            const_cast<spacer_wall_stopwatch*>(this)->stop(); 
            /* update m_time */ 
            const_cast<spacer_wall_stopwatch*>(this)->start();
        }
        return static_cast<double>(m_time)/static_cast<double>(1000000000ull); 
    }

    double get_current_seconds() const { 
        return get_seconds(); 
    }
};
}

#else // Linux 

#include<ctime>

namespace spacer {
class spacer_wall_stopwatch {
    unsigned long long m_time; // elapsed time in ns
    bool               m_running;
    struct timespec    m_start;
    
public:
    spacer_wall_stopwatch():m_time(0), m_running(false) {
    }

    ~spacer_wall_stopwatch() {}
    
    void reset() {
        m_time = 0ull;
    }
    
    void start() {
        if (!m_running) {
            clock_gettime(CLOCK_MONOTONIC, &m_start);
            m_running = true;
        }
    }

    void stop() {
    if (m_running) {
            struct timespec _stop;
            clock_gettime(CLOCK_MONOTONIC, &_stop);
            m_time += (_stop.tv_sec - m_start.tv_sec) * 1000000000ull;
	    if (m_time != 0 || _stop.tv_nsec >= m_start.tv_nsec)
	      m_time += (_stop.tv_nsec - m_start.tv_nsec);
            m_running = false;
        }
    }

    double get_seconds() const { 
        if (m_running) {
            const_cast<spacer_wall_stopwatch*>(this)->stop(); 
            /* update m_time */ 
            const_cast<spacer_wall_stopwatch*>(this)->start();
        }
        return static_cast<double>(m_time)/static_cast<double>(1000000000ull); 
    }

    double get_current_seconds() const { 
        return get_seconds(); 
    }

    static spacer_wall_stopwatch & get_global_stopwatch()
    {
        static spacer_wall_stopwatch w;
        return w;
    }
    static void start_global_stopwatch()
    {
        get_global_stopwatch().start();
    }
    static double get_global_stopwatch_seconds()
    {
        return get_global_stopwatch().get_seconds();
    }
};
} //namespace spacer

#endif


#endif
