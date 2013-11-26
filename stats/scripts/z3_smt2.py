#!/usr/bin/env python

import z3
import sys
import stats
import subprocess

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
    p.add_argument ('--order-children', type=int, dest='order_children', help='Order of processing children in non-linear rules', default=0)

    return p.parse_args (argv)

def stat (key, val): stats.put (key, val)

def main (argv):
    args = parseArgs (argv[1:])
    stat ('Result', 'UNKNOWN')

    z3_args = 'z3'

    if not args.pp:
        print 'No pre-processing'
        z3_args += ' fixedpoint.slice=false'
        z3_args += ' fixedpoint.inline_linear=false'
        z3_args += ' fixedpoint.inline_eager=false'

    print 'Engine: ', args.engine

    if (args.validate):
        z3_args += ' fixedpoint.validate_result=true'
    else:
        z3_args += ' fixedpoint.validate_result=false'

    if (args.answer):
        z3_args += ' fixedpoint.print_answer=true'

    z3_args += ' fixedpoint.engine='
    z3_args += args.engine


    z3_args += ' fixedpoint.use_farkas=true'
    z3_args += ' fixedpoint.generate_proof_trace=false'
    z3_args += ' fixedpoint.use_utvpi=false'

    z3_args += ' fixedpoint.order_children=' + str(args.order_children)

    z3_args += ' ' + args.file


    if len(args.trace) > 0:
        print 'Enable trace: ',
        for t in args.trace.split (':'):
            print t,
            z3_args += ' -tr:{}'.format (t)
        print 
        stats.put ('Trace', args.trace)

    print z3_args

    with stats.timer ('Query'):
        popen = subprocess.Popen(z3_args.split (), stdout=subprocess.PIPE)
        popen.wait()
        res = popen.stdout.read()
    res = res[:-1] # strip off the newline
    print 'Result:', res

#    with stats.timer ('Parse'):
#        q = fp.parse_file (args.file)
#
#    #print fp
#    with stats.timer ('Query'):
#        res = fp.query (q[0])

    if res == 'sat': stat ('Result', 'SAFE')
    elif res == 'unsat': stat ('Result', 'CEX')
    
if __name__ == '__main__':
    try:
        res = main (sys.argv)
    finally:
        stats.brunch_print ()
    sys.exit (res)

