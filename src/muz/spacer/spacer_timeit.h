/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    timeit.h

Abstract:

    Support for timers.

Author:

    Nikolaj Bjorner (nbjorner) 2006-09-22

Revision History:

    Leonardo de Moura (leonardo) 2011-04-27
    Rewrote using stopwatches, added support for tracking memory

--*/
#ifndef _SPACER_TIMEIT_H_
#define _SPACER_TIMEIT_H_

namespace spacer {
class spacer_timeit {
    struct imp;
    imp *  m_imp;
public:
    spacer_timeit(bool enable, char const * msg, std::ostream & out = std::cerr, 
        class spacer_wall_stopwatch * accumulated_time = NULL );
    ~spacer_timeit();
};
}

#endif
