from z3 import *

I = IntSort()
B = BoolSort()

trace = True
linear = False

z3.set_option (verbose=0)

if trace:
    z3.enable_trace ('spacer')
    #z3.enable_trace ('pdr')
    z3.enable_trace ('dl')
    z3.enable_trace ('smt-relation')

x,y = Ints ('x y')
P1 = Function ('A', I, B)
P2 = Function ('B', I, B)
P3 = Function ('C', I, B)
E = Function ('E', B)

fp = Fixedpoint ()
fp.set (engine='spacer', use_farkas=True,generate_proof_trace=False)
fp.set (slice=False, inline_linear=False, inline_eager=False)

fp.declare_var (x,y)
fp.register_relation (P1,P2,P3,E)

if linear:
    fp.rule (P1(1))
    fp.rule (P2(x), [P1(x), x<y, y>1])
    fp.rule (E (), [P2(x), x>0])
else:
    fp.rule (P1(1))
    fp.rule (P2(2))
    fp.rule (P3(x), [P2(y), P1(x), x<=y])
    fp.rule (E (), [P3(x), x>0])

print fp.query (E())
print fp.get_answer ()
