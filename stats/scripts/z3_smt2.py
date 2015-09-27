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
    ## options used for cav'15 paper
    'cav15': ['--use-heavy-mev', '--keep-obligations',
              '--flexible-trace'],
	
    ## three nodes in the spacer job each assigned a differnt profile
    'trifecta': ['--jobsize','3','--distprofile', 'def,ic3,gpdr'],
    'trifectar1k': ['--jobsize','3','--distprofile', 'def,ic3,gpdr', '--restart', '1000'],
    
    ## use distributed mode CLI, but not running distributed, use just one node
    'solodistdef': ['--jobsize','1','--distprofile', 'def'],
    'solodistgpdr': ['--jobsize','1','--distprofile', 'gpdr'],
    'solodistic3': ['--jobsize','1','--distprofile', 'ic3'],

    ## these are just solodist, but in experiments we are changing from the
    ## default 16 cores per machine (1 process per machine) to 5 cores per
    ## machine, this should match the distributed profiles that fork 3 jobs
    ##  we give differnt profile names so runs can be differntiated
    'solodist5cpudef': ['--jobsize','1','--distprofile', 'def'],
    'solodist5cpugpdr': ['--jobsize','1','--distprofile', 'gpdr'],
    'solodist5cpuic3': ['--jobsize','1','--distprofile', 'ic3'],

    # solo distributed variants with restarts 
    'solodistdefr1k': ['--jobsize','1','--distprofile', 'def', '--restart','1000'],
    'solodistgpdr1k': ['--jobsize','1','--distprofile', 'gpdr', '--restart','1000'],
    'solodistic3r1k': ['--jobsize','1','--distprofile', 'ic3', '--restart','1000'],

    ## distributed mode CLI, but running two copies of def
    'dualdistdef': ['--jobsize','2','--distprofile', 'def,def'],

    ## distributed mode CLI, but running two copies of def
    'tridistdef': ['--jobsize','3','--distprofile', 'def,def,def'],

    ## distributed mode CLI, n copies of ic3
    'tridistic3': ['--jobsize','3','--distprofile', 'ic3,ic3,ic3'],
    'octdistic3': ['--jobsize','8','--distprofile', 'ic3,ic3,ic3,ic3,ic3,ic3,ic3,ic3'],

    ## distributed mode CLI, three copies of gpdr
    'tridistgpdr': ['--jobsize','3','--distprofile', 'gpdr,gpdr,gpdr']
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
    p.add_argument ('--pve',
                    help='Enable propagate_variable_equivalences in tail_simplifier',
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
    p.add_argument ('--reach-dnf', dest='reach_dnf', 
                    help='Keep reachability facts in DNF', 
                    action='store_true', default=False)
    p.add_argument ('--no-z3', dest='no_z3',
                    help='stop before running z3', default=False,
                    action='store_true')
    p.add_argument ('--cpu', dest='cpu', type=int,
                    action='store', help='CPU time limit (seconds)', default=-1)
    p.add_argument ('--mem', dest='mem', type=int,
                    action='store', help='MEM limit (MB)', default=-1)   
    p.add_argument ('--jobsize', dest='jobsize', type=int,
                    action='store', help='number of nodes in GASNet job', default=-1)   
    p.add_argument ('--distprofile', dest='distprofile',
                    action='store', help='distribution profile for spacer', default=None)
    p.add_argument ('--gasnet-spawnfn', dest='gasnet_spawnfn',
                    action='store', help='GASNet spawning mode, used for launching job on UDP conduit', default='L')
    p.add_argument ('--verify-msgs', dest='verify_msgs',
                    action='store_true', help='Compute hashes and send reciept confirmation for all messages', default=False)
    p.add_argument ('--restart', dest='restart', type=int, default=-1,
                    action='store', help='restart z3 nodes after performing given ammount of work budget, or -1 to disable restarts')

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

    if args.jobsize != -1:
        z3_args += ' %d' % int(args.jobsize)

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

    if args.pve:
        z3_args += ' fixedpoint.xform.tail_simplifier_pve=true'
    else:
        z3_args += ' fixedpoint.xform.tail_simplifier_pve=false'
        
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
        z3_args += ' fixedpoint.print_statistics=true'

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

    if args.reach_dnf:
        z3_args += ' fixedpoint.spacer.reach_dnf=true'
    else:
        z3_args += ' fixedpoint.spacer.reach_dnf=false'
        
    if args.distprofile:
        z3_args += ' -profile:%s' % args.distprofile

    if args.gasnet_spawnfn:
        os.environ['GASNET_SPAWNFN'] = args.gasnet_spawnfn

    if (args.verify_msgs):
        z3_args += ' fixedpoint.gasnet.verify_msgs=true'

    if args.restart > -1:
        z3_args += ' fixedpoint.pmuz.node_work_budget=%d' % args.restart
        z3_args += ' fixedpoint.pmuz.node_restarts=true'

        
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
        self.stdout = None

    def run(self):
        def set_limits ():
            import resource as r    
            if self.cpu > 0:
                r.setrlimit (r.RLIMIT_CPU, [self.cpu, self.cpu])
            if self.mem > 0:
                mem_bytes = self.mem * 1024 * 1024
                r.setrlimit (r.RLIMIT_AS, [mem_bytes, mem_bytes])
                
        self.p = subprocess.Popen(self.cmd, 
                stdout=subprocess.PIPE,
                preexec_fn=set_limits)
        self.stdout, unused = self.p.communicate()

    def Run(self):
        returncode=19

        try:
            self.start()

            if self.cpu > 0:
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
            returncode = self.p.returncode

        except Exception as e:
            print 'Error wall watching cmd execution:', e.message
            returncode = 20


        return returncode


def main (argv):
    ## add directory containing this file to the PATH
    os.environ ['PATH'] =  os.path.dirname (os.path.realpath (__file__)) + \
                           os.pathsep + os.environ['PATH']

    returncode = 13
    args = parseArgs (argv[1:])
    stat ('Result', 'UNKNOWN')

    z3_args = compute_z3_args (args)
    print z3_args

    if args.no_z3: return returncode

    stat ('File', args.file)
    stat ('base', os.path.basename (args.file))

    cmd = RunCmd(z3_args.split(), args.cpu, args.mem)
    with stats.timer ('Query'):
        returncode = cmd.Run()
    res = cmd.stdout

    if res is None:
        res = 'unknown'
    elif 'unsat' in res:
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
    res = 14
    try:
        res = main (sys.argv)
    finally:
        stats.brunch_print ()
    sys.exit (res)

