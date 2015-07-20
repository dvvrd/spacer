#!/usr/bin/env python

import sys
import stats
import subprocess
import os.path
import threading
import itertools
import hashlib
import pprint
import random
import time

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

    
    ## use distributed mode CLI, but not running distributed, use just one node
    'solodistdef': ['--jobsize','1','--distprofile', 'def'],
    'solodistgpdr': ['--jobsize','1','--distprofile', 'gpdr'],
    'solodistic3': ['--jobsize','1','--distprofile', 'ic3'],
    'origsolodistdef': ['--pve', '--jobsize','1','--distprofile', 'def'],
    'origsolodistgpdr': ['--pve', '--jobsize','1','--distprofile', 'gpdr'],
    'origsolodistic3': ['--pve', '--jobsize','1','--distprofile', 'ic3'],

    'solodistOc1def': ['--jobsize','1','--distprofile', 'Oc1def'],
    'solodistOc1gpdr': ['--jobsize','1','--distprofile', 'Oc1gpdr'],
    'solodistOc1ic3': ['--jobsize','1','--distprofile', 'Oc1ic3'],

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

    ## three nodes in the spacer job each assigned a differnt profile
    'trifecta': ['--jobsize','3','--distprofile', 'def,ic3,gpdr'],
    'triOc1fecta': ['--jobsize','3','--distprofile', 'Oc1def,Oc1ic3,Oc1gpdr'],
    'trifectar1k': ['--jobsize','3','--distprofile', 'def,ic3,gpdr', '--restart', '1000'],
    'triLtrfecta': ['--jobsize','3','--distprofile', 'Ltrdef,Ltric3,Ltrgpdr'],
    'triLtlfecta': ['--jobsize','3','--distprofile', 'Ltldef,Ltlic3,Ltlgpdr'],
    'triLtofecta': ['--jobsize','3','--distprofile', 'Ltodef,Ltoic3,Ltogpdr'],
    'triLtxfecta': ['--jobsize','3','--distprofile', 'Ltxdef,Ltxic3,Ltxgpdr'],
    'triLtnfecta': ['--jobsize','3','--distprofile', 'Ltndef,Ltnic3,Ltngpdr'],
    'triLtmfecta': ['--jobsize','3','--distprofile', 'Ltmdef,Ltmic3,Ltmgpdr'],

    ## distributed mode CLI, but running two copies of def
    'tridistdef': ['--jobsize','3','--distprofile', 'def,def,def'],
    ## distributed mode CLI, n copies of ic3
    'tridistic3': ['--jobsize','3','--distprofile', 'ic3,ic3,ic3'],
    ## distributed mode CLI, three copies of gpdr
    'tridistgpdr': ['--jobsize','3','--distprofile', 'gpdr,gpdr,gpdr'],

    'tridistOc1ic3': ['--jobsize','3','--distprofile', 'Oc1ic3,Oc1ic3,Oc1ic3'],

    'hexfecta': ['--jobsize','6','--distprofile','def,ic3,gpdr,Oc1def,Oc1ic3,Oc1gpdr'],

    'octdistic3': ['--jobsize','8','--distprofile', 'ic3,ic3,ic3,ic3,ic3,ic3,ic3,ic3'], 

    'nonfecta': ['--jobsize','6','--distprofile','def,ic3,gpdr,Oc1def,Oc1ic3,Oc1gpdr,Eatdef,Eatic3,Eatgpdr'],


    ## options used for cav'15 paper
    'cav15': ['--use-heavy-mev', '--keep-obligations',
              '--flexible-trace'],
    
}

profile_base = [ "def","ic3","gpdr" ];

profile_excl = {
        'Lt' : ["Ltr","Ltl","Lto","Ltx","Ltn","Ltm"],
        'Oc' : ["Oc1"],
        'Eat': ["Eat"],
        'Rdt': ["Rdt"]
        }

slavecmdfile = None

def inodeprofiles():
    for i in profile_base: yield i
    for n in xrange(1,len(profile_excl)+1):
        for combo in itertools.combinations(profile_excl.keys(), n):
            biglist = ( profile_excl[x] for x in combo )
            for possibility in itertools.product(*biglist):
                for base in profile_base:
                    yield ''.join(sorted(possibility)) + base


# generate profiles based on all combinations of distprofiles
def iprofiles(n):
    nodeprofiles = [ x for x in inodeprofiles() ] 
    for combo in itertools.combinations(nodeprofiles, n):
        yield ','.join(sorted(combo))

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
    p.add_argument ('--verbose-file', help='path to file where verbose log is written', default=None)
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
    p.add_argument ('--print-profiles', dest='print_profiles', type=int, default=-1,
                    action='store', help='print avilable profiles for specified number of nodes, then exit')
    p.add_argument ('--mesos-master', dest='mesos_master',
                    action='store', help='The host and port of the mesos master, setting this indicates that psmcframework will be used'
                    ' to launch the job on mesos, and the --gasnet-spawnfn then should not be specified', default=None)
    p.add_argument ('--mesos-root', dest='mesos_root',
                    action='store', help='The mesos installation root, needed when specifying --mesos-master', default=None)
    p.add_argument ('--mesos-name', dest='mesos_name', default='z3_smt2.py_framework', action='store',
            help='Name for the mesos framework, identifies the job in mesos, and controls output dir name')
    p.add_argument ('--mesos-output-dir', dest='mesos_outdir', default='.', action='store',
            help='copy outputs from mesos slaves to this directory')
    p.add_argument ('--mesos-verbose', dest='mesos_verbose', default=0, action='store',
            help='verbosity of the portfolio mesos framework')
    p.add_argument ('--mesos-output-summary', dest='mesos_output_sumary', default=False, action='store_true',
            help='Show a summary of all completed portfolio tasks')

    # HACK: profiles as a way to provide multiple options at once
    global profiles
    nargv = []
    in_p = False
    in_rp = False

    for s in argv:
        if in_p:
            print 'assigning for', s
            if s in profiles:
                stat('profile', s)
                nargv.extend (profiles[s])
            elif s.endswith(tuple(profiles)) and all([x.endswith(tuple(profiles)) for x in s.split(',')]):
                stat('profile', s)
                nargv.extend(['--jobsize',str(len(s.split(','))),'--distprofile',s])                
            elif s.startswith("random"):
                jobsize = int (s[len("random"):])
                subset = list(iprofiles(1))
                rp = ','.join([random.choice(subset) for x in range(jobsize)])
                stat('profile', s)
                nargv.extend(['--jobsize',str(jobsize),'--distprofile',rp])
            else:
                print 'WARNING: not an known profile, or an unknown profile ending with:', profile_base
                sys.exit(1)
            in_p = False
        elif in_rp:
            jobsize = int(s)
            subset = list(iprofiles(jobsize))
            rp = random.choice(subset)
            stat('profile', rp)
            nargv.extend(['--jobsize',s,'--distprofile',rp])
            in_rp = False
        elif s == '-p': 
            in_p = True
        elif s == '-rp':
            in_rp = True
        else: nargv.append (s)
        
    if in_p: 
        print 'WARNING: missing profile or number of nodes'
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
    z3_args = which ('pmuz')

    if z3_args is None:
        print 'No executable named "z3" found in current directory or PATH'
        return

    if args.jobsize != -1:
        z3_args += ' %d' % int(args.jobsize)

    z3_args += ' -v:' + str(args.verbose)

    if args.verbose_file is not None:
        z3_args += ' -vo:' + str(args.verbose_file)

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
        print 'GASNET_SPAWNFN is', os.environ['GASNET_SPAWNFN']
        if args.gasnet_spawnfn == "C":
            global slavecmdfile
            if which('portfolio_framework') is None:
                raise Exception("portfolio_framework is not in current dir or in PATH")
            if args.mesos_master is None:
                raise Exception("--mesos-master is not set, could be like --mesos-master=n001.etc.sei.cmu.edu:5050")
            if args.mesos_root is None:
                raise Exception("--mesos-root is not set, could be like --mesos-root=/opt/mesos")
            slavecmdfile = os.path.join('/tmp',
                    os.path.basename(args.file) + '.slave.' + str(int(time.time()*100)))
            os.environ['GASNET_CSPAWN_CMD']="echo \"%%N\n%%C\n%%D\"> %s" % slavecmdfile

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

def try_read_slavecmdfile(slavecmdfile):
    content = []
    try:
        with open(slavecmdfile) as f:
                content = f.readlines()
        if len(content) == 3:
            slot = content[1].find('/bin/sh -c')
            if slot != -1:
                content[1] = content[1][slot+len('/bin/sh -c'):]

            slot = content[1].find('||')
            if slot != -1:
                content[1] = content[1][0:slot]
        content = [x.strip() for x in content]
    except IOError:
        pass
    return content

def compute_portfolio_args(args,portfolio_size,command):
    pfargs = []
    portfolio_framework = which("portfolio_framework")
    pfargs.append(portfolio_framework)
    pfargs.append('--portfolio-size=%s' % portfolio_size)
    pfargs.append('--mesos-master=%s' % args.mesos_master)
    pfargs.append('--mesos-root=%s' % args.mesos_root)
    pfargs.append('--cpus-per-cmd=1')
    pfargs.append('--mb-mem-per-cmd=%s' % args.mem)
    pfargs.append('--name=%s' % args.mesos_name)
    pfargs.append('--output-path=%s' % args.mesos_outdir)
    pfargs.append('--copy-outputs')
    pfargs.append('--verbose=%d' % int(args.mesos_verbose))
    pfargs.append('--')
    pfargs.append('timeout %d' % args.cpu)
    pfargs.append(command)

    return ' '.join(pfargs)




# inspred from:
# http://stackoverflow.com/questions/4158502/python-kill-or-terminate-subprocess-when-timeout
class RunCmd(threading.Thread):
    def __init__(self, cmd, cpu, mem, args, slavecmdfile):
        threading.Thread.__init__(self)
        self.cmd = cmd 
        self.cpu = cpu
        self.mem = mem
        self.args = args
        self.p = None
        self.stdout = None
        self.portfolio = None
        self.slavecmdfile = slavecmdfile

    def run(self):
        def set_limits ():
            import resource as r    
           #In distributed mode, We measure by wall time.  setrlimit is documented
           #as limiting CPU time
           #if self.cpu > 0:
           #    r.setrlimit (r.RLIMIT_CPU, [self.cpu, self.cpu])

            if self.mem > 0:
                mem_bytes = self.mem * 1024 * 1024
                r.setrlimit (r.RLIMIT_AS, [mem_bytes, mem_bytes])
                
        self.p = subprocess.Popen(self.cmd,
                stdout=subprocess.PIPE,
                preexec_fn=set_limits)
        pfo = None
        if self.slavecmdfile is not None:
            scfcontent = []
            while len(scfcontent) != 3:
                scfcontent = try_read_slavecmdfile(self.slavecmdfile)

            portfolio_args = compute_portfolio_args(
                self.args,int(scfcontent[0]),scfcontent[1])

            print 'portfolio command:'
            print portfolio_args

            self.portfolio_framework = subprocess.Popen(
                    portfolio_args.split(),
                    stdout=subprocess.PIPE)

            pfo, pfe = self.portfolio_framework.communicate()
        o,e = self.p.communicate()

        self.stdout = "\n".join([o,pfo]).strip()

    def Run(self):
        returncode=19

        try:
            self.start()

            if self.cpu > 0:
                self.join(self.cpu)
            else:
                self.join()

            if self.is_alive():
                print 'z3 has most likely timed out'
                self.p.terminate()
                if self.portfolio:
                    self.portfolio.terminate()
                self.join(5)

            if self.is_alive():
                print 'z3 is still alive after attempt to terminate, sending kill'
                self.p.kill()
                if self.portfolio:
                    self.portfolio.kill()

            returncode = self.p.returncode

        except Exception as e:
            print 'Error when watching cmd execution:', e.message
            returncode = 20

        print "exit code is", self.p.returncode
        return returncode


def process_task_stdout(ofilepath):
    outdict = {}
    maintimesearchstr = 'BRUNCH_STAT main_time '
    nodeprofilesearchstr = 'BRUNCH_STAT node_profile '
    statussearchstr = 'Command exited with status '

    with open(ofilepath) as ofile:
        for line in ofile:
            # finishes will store a list of tuples of info about finished tasks
            if 'VERIFICATION SUCCESSFUL' in line:
                outdict['pmuz_result'] = 'VERIFICATION SUCCESSFUL'
            elif 'VERIFICATION FAILED' in line:
                outdict['pmuz_result'] = 'VERIFICATION FAILED'
            elif 'VERIFICATION UNDEDFINED' in line:
                outdict['pmuz_result'] = 'VERIFICATION UNDEDFINED'
            elif maintimesearchstr in line:
                maintimestr = line[len(maintimesearchstr):].strip()
                outdict['main_time'] = float(maintimestr)
            elif nodeprofilesearchstr in line:
                outdict['node_profile'] = line[len(nodeprofilesearchstr):].strip()
            elif statussearchstr in line:
                statusstr = line[len(statussearchstr):].strip()
                slot = statusstr.find(' ')
                if slot != -1 and slot > 0:
                    statusstr = statusstr[:slot].strip()
                    outdict['status'] = int(statusstr)

    return outdict

def main (argv):
    ## add directory containing this file to the PATH
    os.environ ['PATH'] =  os.path.dirname (os.path.realpath (__file__)) + \
                           os.pathsep + os.environ['PATH']

    returncode = 13
    args = parseArgs (argv[1:])

    if args.print_profiles != -1:
        for x in iprofiles(args.print_profiles):
            print x
        sys.exit(0)

    stat ('Result', 'UNKNOWN')

    z3_args = compute_z3_args (args)
    print z3_args

    if args.no_z3: return returncode

    stat ('File', args.file)
    stat ('base', os.path.basename (args.file))

    cmd = RunCmd(z3_args.split(), args.cpu, args.mem, args, slavecmdfile)
    with stats.timer ('Query'):
        returncode = cmd.Run()
    res = cmd.stdout
    print 'BEGIN SUBPROCESS STDOUT'
    print res;
    print 'END SUBPROCESS STDOUT'
    # begin special handling to ger mesos task
    # if this was a mesos portfolio framework run
    if slavecmdfile is not None:
        lines = res.split("\n")
        finished_tasks = {}
        first_mentioned_task = None
        # determine all of the finished tasks that look like they acruallt
        # completed running a pmuz
        for line in lines:
            searchstr = "%s finished task: " % args.mesos_name
            if searchstr in line:
                taskidstr = line[len(searchstr):].strip()
                taskid = int(taskidstr)
                ofilepath = os.path.join(
                        args.mesos_outdir,
                        "%s.%d.stdout" % (args.mesos_name,taskid))
                taskdict = process_task_stdout(ofilepath)
                if taskid in finished_tasks:
                    print 'ERROR : Same task finished twice?'
                    returncode = 1
                    exit(returncode)
                finished_tasks[taskid] = taskdict
                if first_mentioned_task is None: first_mentioned_task = taskid

        if args.mesos_output_sumary:
            print 'Finished Task Summary:'
            for k,v in finished_tasks.items():
                print ' Task',k,':',v
            
        # determine the tasks that have all the expected information gleaned from        
        # stdout, these should be tasks that didn't get a kill signal in time to
        # finish on thier own, and pick which one is the fastest
        fastesttask = None
        fully_finished_tasks = {}
        for k,v in finished_tasks.items():
            if 'pmuz_result' not in v: continue
            if 'status' not in v: continue
            if 'main_time' not in v: continue
            fully_finished_tasks[k] = v

            if fastesttask is None or v['main_time'] < finished_tasks[fastesttask]['main_time']:
                fastesttask = k

        # check that all returned the same answer as the fastest task
        if fastesttask is not None:
            for k,v in fully_finished_tasks.items():            
                if v['pmuz_result'] != fully_finished_tasks[fastesttask]['pmuz_result']:
                    print 'ERROR: Tasks to not agree on answer: ', fully_finished_tasks
                    returncode = 1
                    exit(returncode)
        else:
            # the fastest task could not be determined (by looking for the stat main_time
            # in this case we will pick the best representative we can, the first one to print
            fastesttask = first_mentioned_task
            print 'Fastest completing task could not be reliably determined, chose to use task', fastesttask


        # display the stdout of the winner
        if fastesttask is None:
            res = ""
            print 'There were no finished portfolio tasks'
            if returncode == 0: returncode = 5
        else:
            # adopt the return code of the fastest process
            if 'status' not in finished_tasks[fastesttask]:
                print 'WARNING: Task finished without Status'
                if returncode == 0: returncode = 5
            else:
                returncode = finished_tasks[fastesttask]['status']

            if 'main_time' not in finished_tasks[fastesttask]:
                print 'WARNING: Task finished without main_time'
            else: stat('main_time',finished_tasks[fastesttask]['main_time'])

            if 'node_profile' not in finished_tasks[fastesttask]:
                print 'WARNING: Task finished without node_profile'
            else: stat('node_profile',finished_tasks[fastesttask]['node_profile'])
            

            ofilepath = os.path.join(
                    args.mesos_outdir,
                    "%s.%d.stdout" % (args.mesos_name,fastesttask))
            print 'Using output from portfolio task', fastesttask, ":", ofilepath
            with open(ofilepath) as ofile:
                res = ofile.read()

        print 'BEGIN PORTFOLIO TASK STDOUT'
        print res
        print 'END PORTFOLIO TASK STDOUT'
        # end special handling to ger mesos task

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
    sys.stdout.flush()
    sys.stderr.flush()
    sys.exit (res)

