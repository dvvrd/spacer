import sys
import argparse

def parse_args (argv):
  argparser = argparse.ArgumentParser()

  argparser.add_argument('--lvl',
                         action='store',
                         type=int,
                         default=0,
                         help='num levels')

  args = argparser.parse_args (argv)
  return args


def populate (n):
    rules = []

    for i in range (n+1):
        # input g is true

        # 3-bit counter
        rules.append ("(rule (L{} false false false))".format (i))

        rules.append ("(rule (=> (and (L{} a b c)\n"
                      "               (not a))\n"
                      "          (L{} true b c)))".format (i, i))

        rules.append ("(rule (=> (and (L{} a b c)\n"
                      "               a\n"
                      "               (not b))\n"
                      "          (L{} false true c)))".format (i, i))

        rules.append ("(rule (=> (and (L{} a b c)\n"
                      "               a b\n"
                      "               (not c))\n"
                      "          (L{} false false true)))".format (i, i))

        rules.append ("(rule (=> (L{} true true true)\n"
                      "          (Lvl{} true false)))".format (i, i))


        # input g is false

        if i>0:
            rules.append ("(rule (=> (and (Lvl{} false g1)\n"
                          "               (Lvl{} g1 g2))\n"
                          "          (Lvl{} false (not g2))))"
                           .format (i-1, i-1, i))
        else:
            rules.append ("(rule (Lvl0 false true))")


    # main
    rules.append ("(rule (=> (and (Lvl{} g1 g2)\n"
                  "               (Lvl{} g2 g3)\n"
                  "          )\n"
                  "          E))".format (n, n))

    return rules


def main (argv):
    args = parse_args (argv[1:])
    l = args.lvl
    
    decls = []
    # vars
    decls.append ("(declare-var a Bool)")
    decls.append ("(declare-var b Bool)")
    decls.append ("(declare-var c Bool)")
    decls.append ("(declare-var g1 Bool)")
    decls.append ("(declare-var g2 Bool)")
    decls.append ("(declare-var g3 Bool)")
    # rels
    decls.append ("(declare-rel E ())")
    for i in range (l+1):
        decls.append ("(declare-rel L{} (Bool Bool Bool))".format (i))
        decls.append ("(declare-rel Lvl{} (Bool Bool))".format (i))
    
    rules = populate (l)
    
    
    # output
    for d in decls:
        print d
    for r in rules:
        print r
    
    print "(query E)"



if __name__ == '__main__':
  # unbuffered output
  import os
  sys.stdout = os.fdopen (sys.stdout.fileno (), 'w', 0)  
  sys.exit (main(sys.argv))
