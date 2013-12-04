#!/usr/bin/env python

import z3
import sys
import stats

def parseArgs (argv):
    import argparse as a
    p = a.ArgumentParser (description='Z3 Datalog Frontend')
    
    p.add_argument ('file', metavar='BENCHMARK', help='Benchmark file')
    p.add_argument ('--pp', 
                    help='Enable default pre-processing', 
                    action='store_true', default=False)
    p.add_argument ('--validate', help='Enable validation',
                    action='store_true', default=False)
    p.add_argument ('--trace', help='Trace levels to enable (spacer, pdr, dl,'
                                    'smt-relation, etc.)', 
                    default='')
    p.add_argument ('--answer', help='Print answer', action='store_true',
                    default=False)
    p.add_argument ('--engine', help='Datalog Engine (pdr/spacer)', default='spacer')
    p.add_argument ('--verbose', help='Z3 verbosity', default=0)
    p.add_argument ('--use-utvpi', dest='use_utvpi', help='use utvpi/diff-logic '
                                                          'solvers, if applicable',
                    action='store_true', default=False)
    p.add_argument ('--eager-reach-check', dest='eager_reach_check',
                    help='eagerly use reachability facts for every local query',
                    action='store_true', default=False)

    return p.parse_args (argv)

def stat (key, val): stats.put (key, val)

def main (argv):
    args = parseArgs (argv[1:])
    stat ('Result', 'UNKNOWN')
    z3.set_option (verbose=args.verbose)
    ctx = z3.Context ()
    fp = z3.Fixedpoint (ctx=ctx)
    if not args.pp:
        print 'No pre-processing'
        fp.set (slice=False)
        fp.set (inline_linear=False)
        fp.set (inline_eager=False)

    print 'Engine: ', args.engine

    fp.set (validate_result=args.validate)
    fp.set (engine=args.engine, use_farkas=True, generate_proof_trace=False)
    fp.set (use_utvpi=args.use_utvpi)
    fp.set (eager_reach_check=args.eager_reach_check)

    with stats.timer ('Parse'):
        q = fp.parse_file (args.file)

    if len(args.trace) > 0:
        print 'Enable trace: ',
        for t in args.trace.split (':'):
            print t,
            z3.enable_trace (t)
        print 
        stats.put ('Trace', args.trace)
    #print fp
    with stats.timer ('Query'):
        res = fp.query (q[0])

    if res == z3.sat: stat ('Result', 'CEX')
    elif res == z3.unsat: stat ('Result', 'SAFE')

    if args.answer:
        print 'The answer is:'
        print fp.get_answer ()
    
if __name__ == '__main__':
    try:
        res = main (sys.argv)
    finally:
        stats.brunch_print ()
    sys.exit (res)

