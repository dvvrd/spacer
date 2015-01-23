#!/usr/bin/env python

import sys
import stats
import subprocess

def parseArgs (argv):
    import argparse as a
    p = a.ArgumentParser (description='Z3 Datalog Frontend')
    
    p.add_argument ('file', metavar='BENCHMARK', help='Benchmark file')
    p.add_argument ('--slice', 
                    help='Enable slicing', 
                    action='store_true', default=False)
    p.add_argument ('--inline', 
                    help='Enable inlining', 
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
    p.add_argument ('--no-utvpi', dest='no_utvpi', help='do not check for utvpi/diff-logic',
                    action='store_true', default=False)
    p.add_argument ('--lazy-reach-check', dest='lazy_reach_check',
                    help='use reachability facts lazily',
                    action='store_true', default=False)
    p.add_argument ('--validate-theory-core', dest='validate_theory_core',
                    help='validate every theory core',
                    action='store_true', default=False)
    p.add_argument ('--print-stats', dest='print_stats',
                    help='flag to print stats',
                    action='store_true', default=False)
    p.add_argument ('--dfs', dest='dfs',
                    help='use dfs instead of bfs',
                    action='store_true', default=False)
    p.add_argument ('--order-children', dest='order_children',
                    help='0 (rtol), 1 (ltor)', default=0)
    p.add_argument ('--array-blast-full', dest='array_blast_full',
                    help='elim local array variables using QE',
                    action='store_true', default=False)
    p.add_argument ('--array-blast', dest='array_blast',
                    help='elim local array variables using heuristics',
                    action='store_true', default=False)
    p.add_argument ('--use-heavy-mev', dest='use_heavy_mev',
                    help='use heavy model evaluation routines for arrays',
                    action='store_true', default=False)
    p.add_argument ('--smt2lib', dest='smt2lib',
                    help='input smt2 file is in smt2lib format (and not datalog)',
                    action='store_true', default=False)
    p.add_argument ('--flexible-trace', dest='flexible_trace',
                    help='enable generation of long cexes',
                    action='store_true', default=False)
    p.add_argument ('--skip-propagate', dest='skip_propagate',
                    help='skip propagation phase, emulating BMC',
                    action='store_true', default=False)
    p.add_argument ('--keep-obligations', dest='keep_obligations',
                    help='keep obligations across levels',
                    action='store_true', default=False)
    p.add_argument ('--max-lvl', dest='max_lvl',
                    help='max query level', type=int,
                    action='store', default=-1)

    return p.parse_args (argv)

def stat (key, val): stats.put (key, val)

import os.path

def isexec (fpath):
    if fpath == None: return False
    return os.path.isfile(fpath) and os.access(fpath, os.X_OK) 

def which(program):
    exe_file = os.path.join ('./', program)
    if (isexec (exe_file)): return exe_file
    for path in os.environ["PATH"].split(os.pathsep):
        exe_file = os.path.join(path, program)
        if isexec (exe_file):
            return exe_file
    return None

def main (argv):
    args = parseArgs (argv[1:])
    stat ('Result', 'UNKNOWN')

    z3_args = which ('z3')

    if z3_args is None:
        print 'No executable named "z3" found in current directory or PATH'
        return

    z3_args += ' -v:' + str(args.verbose)

    if not args.slice:
        print 'No slicing'
        z3_args += ' fixedpoint.xform.slice=false'

    if not args.inline:
        print 'No inlining'
        z3_args += ' fixedpoint.xform.inline_linear=false'
        z3_args += ' fixedpoint.xform.inline_eager=false'

    print 'Engine: ', args.engine

    if (args.validate):
        z3_args += ' fixedpoint.pdr.validate_result=true'

    if (args.answer):
        z3_args += ' fixedpoint.print.answer=true'

    z3_args += ' fixedpoint.engine='
    z3_args += args.engine

    if args.no_utvpi:
        z3_args += ' fixedpoint.pdr.utvpi=false'

    if args.lazy_reach_check:
        z3_args += ' fixedpoint.eager_reach_check=false'

    if args.validate_theory_core:
        z3_args += ' fixedpoint.validate_theory_core=true'

    if args.print_stats:
        z3_args += ' fixedpoint.print.statistics=true'

    if args.dfs:
        z3_args += ' fixedpoint.pdr.bfs_model_search=false'

    if int(args.order_children)==1:
        z3_args += ' fixedpoint.order_children=1'

    if args.array_blast:
        z3_args += ' fixedpoint.xform.array_blast=true'

    if args.array_blast_full:
        z3_args += ' fixedpoint.xform.array_blast_full=true'

    if args.use_heavy_mev:
        z3_args += ' fixedpoint.use_heavy_mev=true'

    if args.flexible_trace:
        z3_args += ' fixedpoint.pdr.flexible_trace=true'

    if args.skip_propagate:
        z3_args += ' fixedpoint.pdr.skip_propagate=true'

    if args.keep_obligations:
        z3_args += ' fixedpoint.reset_obligation_queue=false'

    if int(args.max_lvl) >= 0:
        z3_args += ' fixedpoint.pdr.max_level={}'.format (args.max_lvl)

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
    if 'unsat' in res:
        res = 'unsat'
    elif 'sat' in res:
        res = 'sat'
    else:
        res = 'unknown'
    print 'Result:', res

    if res == 'sat':
        if args.smt2lib: stat ('Result', 'SAFE')
        else: stat ('Result', 'CEX')
    elif res == 'unsat':
        if args.smt2lib: stat ('Result', 'CEX')
        else: stat ('Result', 'SAFE')
    
if __name__ == '__main__':
    try:
        res = main (sys.argv)
    finally:
        stats.brunch_print ()
    sys.exit (res)

