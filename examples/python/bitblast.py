import sys
import z3

def bitblast (e):
  ctx = e.ctx
  goal = z3.Goal (ctx=ctx)
  goal.add (z3.simplify (e))
  tactic = z3.Tactic ('bit-blast', ctx=ctx)
  res = tactic.apply (goal, blast_full=True)
  assert (len (res) == 1)
  return res [0].as_expr ()

def parseArgs (argv):
    import argparse as a
    p = a.ArgumentParser (description = 'bitblaster')
    p.add_argument ('file', metavar='FILE', type=str,
                    help = 'Input file')
    p.add_argument ('--no-blast', help='Disable bit blasting',
                    action='store_true', default=False)
    p.add_argument ('--check-sat', help='Run solver',
                    action='store_true', default=False)
    p.add_argument ('-o', metavar='FILE', type=str,
                    help='File to store the formula', default=None)
    args = p.parse_args (argv)
    return args

def main (argv):
    print 'In main'
    args = parseArgs (argv[1:])

    ctx = z3.Context ()
    fmla = z3.parse_smt2_file (args.file, ctx=ctx)

    msg = 'Solving'
    if not args.no_blast:
        msg = msg + ' (blasted)'
        blasted = bitblast (fmla)
    else:
        blasted = fmla
    msg = msg + " ..."

    if args.o <> None:
        with open (args.o, 'w') as f:
            f.write (blasted.sexpr ())


    print msg
    solver = z3.Solver (ctx=ctx)
    solver.add (blasted)
    res = solver.check ()
    print res
    return 0
if __name__ == '__main__':
    sys.exit (main (sys.argv))
