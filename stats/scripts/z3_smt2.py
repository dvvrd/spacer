#!/usr/bin/env python

import sys
import stats
import subprocess
import os.path
import threading

profiles = {
    ## skip propagation but drive the search as deep as possible
    'bmc': ['--skip-propagate', '--use-heavy-mev', 
            '--flexible-trace', '--keep-obligations', 
            '--no-elim-aux'], 
    ## default mode. Eventually this will be the best option to start with
    'def': ['--use-heavy-mev', '--keep-obligations',
            '--flexible-trace', '--no-elim-aux'],
    ## inspired by IC3: there is a priority queue, but it is reset
    ## between propagations
    'ic3': ['--use-heavy-mev', '--flexible-trace', '--no-elim-aux'],
    ## inspired by gpdr: no priority queue. 
    'gpdr': ['--use-heavy-mev', '--no-elim-aux'],
    ## For testing the launching and parsing harness
    'testlaunch': ['--use-heavy-mev', '--keep-obligations',
            '--flexible-trace', '--no-elim-aux','--verbose=1', 
            '--print-stats','--mem=24000', '--cpu=10' ]
}

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
    p.add_argument ('--no-elim-aux', dest='elim_aux', 
                    help='do not eliminate auxiliaries in reachability facts', 
                    action='store_false', default=True)
    p.add_argument ('--elim-aux', dest='elim_aux',
                    help='eliminate auxiliaries in reachability facts',
                    action='store_true')
    p.add_argument ('--no-z3', dest='no_z3',
                    help='stop before running z3', default=False,
                    action='store_true')
    p.add_argument ('--cpu', dest='cpu', type=int,
                    action='store', help='CPU time limit (seconds)', default=-1)
    p.add_argument ('--mem', dest='mem', type=int,
                    action='store', help='MEM limit (MB)', default=-1)   

    # HACK: profiles as a way to provide multiple options at once
    global profiles
    nargv = []
    in_p = False
    for s in argv:
        if in_p:
            if s not in profiles:
                break
            stat('profile', s)
            nargv.extend (profiles[s])
            in_p = False
        elif s == '-p': 
            in_p = True
        else: nargv.append (s)
        
    if in_p: 
        print 'WARNING: missing profile'
        sys.exit (1)
    return p.parse_args (nargv)

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

def compute_z3_args (args):
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

    if args.elim_aux:
        z3_args += ' fixedpoint.spacer.elim_aux=true' 
    else:
        z3_args += ' fixedpoint.spacer.elim_aux=false'
        
    z3_args += ' ' + args.file


    if len(args.trace) > 0:
        print 'Enable trace: ',
        for t in args.trace.split (':'):
            print t,
            z3_args += ' -tr:{}'.format (t)
        print 
        stats.put ('Trace', args.trace)

    return z3_args


# inspred from:
# http://stackoverflow.com/questions/4158502/python-kill-or-terminate-subprocess-when-timeout
class RunCmd(threading.Thread):
    def __init__(self, cmd, cpu, mem):
        threading.Thread.__init__(self)
        self.cmd = cmd 
        self.cpu = cpu
        self.mem = mem
        self.p = None

    def run(self):
        def set_limits ():
            import resource as r    
            if self.cpu > 0:
                r.setrlimit (r.RLIMIT_CPU, [self.cpu, self.cpu])
            if self.mem > 0:
                mem_bytes = self.mem * 1024 * 1024
                r.setrlimit (r.RLIMIT_AS, [mem_bytes, mem_bytes])
                
#       print "In thread, opening process"
        self.p = subprocess.Popen(self.cmd, stdout=subprocess.PIPE,
                                 preexec_fn=set_limits)
#       print "In thread, waiting for exit"
        self.p.wait()
#       print "In thread, z3 has exited"

    def Run(self):
        print "Launching thread"
        self.start()

        if self.cpu > 0:
#           print "Waiting for", self.cpu, 'seconds'
            self.join(self.cpu+5)
        else:
            self.join()

        if self.is_alive():
            print 'z3 is still alive, terminating'
            self.p.terminate()      
            self.join(5)

        if self.is_alive():
            print 'z3 is still alive after attempt to terminate, sending kill'
            self.p.kill()

        return self.p.returncode



def main (argv):
    returncode = 1
    args = parseArgs (argv[1:])
    stat ('Result', 'UNKNOWN')

    z3_args = compute_z3_args (args)
    print z3_args

    if args.no_z3: return returncode

    stat ('File', args.file)
    stat ('base', os.path.basename (args.file))

    with stats.timer ('Query'):
        cmd = RunCmd(z3_args.split(), args.cpu, args.mem)
        returncode = cmd.Run()
    res = cmd.p.stdout.read()

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

    # set returncode    
    stat ('Status', returncode)

    return returncode
    
if __name__ == '__main__':
    try:
        res = main (sys.argv)
    finally:
        stats.brunch_print ()
    sys.exit (res)

