#!/usr/bin/env python

import z3
import z3_utils as z3u
import sys


def parseArgs (argv):
    import argparse

    argp = argparse.ArgumentParser ()
    argp.add_argument ('file', help='File name')
    argp.add_argument ('--out', help='Output file name',
                       default=None)

    return argp.parse_args (argv)


class Rule:

    def __init__ (self, rule_exp):
        self.rule_exp = rule_exp
        self.qvars, self.matrix = z3u.strip_qblock (rule_exp)
        if z3.is_app_of (self.matrix, z3.Z3_OP_IMPLIES):
            self.body = self.matrix.arg (0)
            self.head = self.matrix.arg (1)
        else:
            self.body = None
            self.head = self.matrix

        # body stuff
        self.body_inst = self._get_first_pred_inst (self.body)
        self.body_decl = self._get_inst_decl (self.body_inst)

        # obtain head_decl
        self.head_decl = self.head.decl ()

        # trans
        self.trans = self._get_trans (self.body)

    def _get_first_pred_inst (self, expr):
        if expr is not None and z3.is_and (expr):
            return expr.arg (0)
        return None

    def _get_inst_decl (self, inst):
        if inst is not None:
            return inst.decl ()
        return None

    def _get_trans (self, expr):
        if expr is not None and z3.is_and (expr):
            if expr.num_args () > 1:
                return z3.And (*expr.children () [1:])
            else:
                return z3.BoolVal (True)
        return None

    def has_body_pred (self):
        return self.body is not None

    def get_body_decl (self):
        return self.body_decl

    def get_head_decl (self):
        return self.head_decl

    def get_body_pred_name (self):
        if self.body is None: return ""
        return self.body_decl.name ()

    def get_head_pred_name (self):
        return self.head_decl.name ()

    def get_body_inst (self):
        return self.body_inst

    def get_head (self):
        return self.head

    def get_trans (self):
        return self.trans

    def is_self_loop (self):
        if self.get_body_pred_name () == self.get_head_pred_name ():
            return True
        return False

    def uses_const_in_trans (self, c):
        return z3u.has_const (self.trans, c)

    def __repr__ (self):
        return '{} -> {}'.format (self.get_body_pred_name (),
                                  self.get_head_pred_name ())


def insert_in_dict (d, key, val_entry):
    if key not in d:
        d [key] = list ()
    d [key].append (val_entry)


def remove_from_dict (d, key, val_entry):
    d [key].remove (val_entry)


def parse (fp, decls, rules, self_loops, preds, succs):
    for rule_exp in fp.get_rules ():
        rule = Rule (rule_exp)
        if rule.is_self_loop ():
            insert_in_dict (self_loops, rule.get_head_pred_name (), rule)
        else:
            insert_in_dict (preds, rule.get_head_pred_name (), rule)
            if rule.has_body_pred ():
                insert_in_dict (succs, rule.get_body_pred_name (), rule)
        rules.append (rule)

        name = rule.get_head_pred_name ()
        if name not in decls:
            decls [rule.get_head_pred_name ()] = rule.get_head_decl ()
        if name not in succs:
            succs [name] = list ()
        if name not in preds:
            preds [name] = list ()


def dfs_number (decls, init_pred_name, succs):
    visited = list ()
    todo = list ()
    numbers = dict ()

    todo.append (init_pred_name)
    n = 0
    while len (todo) > 0:
        name = todo.pop ()
        visited.append (name)
        numbers [name] = n; n += 1
        for r in succs [name]:
            succ_name = r.get_head_pred_name ()
            if succ_name not in visited:
                todo.append (succ_name)
    return numbers


# find indices which the loop truly depends on
# if x_i != y_i, or if x_i is used in t, for some loop rule
# P(x) /\ t(x,y) -> P(y), include it;
# otherwise, discard
def find_arg_indices (decl, loop_rules):
    from sets import Set
    indices = Set ()
    for rule in loop_rules:
        from_args = rule.get_body_inst ().children ()
        to_args = rule.get_head ().children ()
        for i in range (decl.arity ()):
            if (from_args [i].decl ().name () != to_args [i].decl ().name ())\
                    or rule.uses_const_in_trans (from_args [i]):
                indices.add (i)
        if len (indices) == decl.arity (): break
    return sorted (list (indices))


def outline_loop (name, decls, rules, self_loops, preds, succs):
    assert name in self_loops
    loop_rules = self_loops [name]
    decl = decls [name]
    arg_indices = find_arg_indices (decl, loop_rules)
    print 'Indices for procedure args:', arg_indices
    arg_sorts = [decl.domain (i) for i in arg_indices]

    # make new procedure
    proc_sorts = arg_sorts + arg_sorts + [decl.range ()]
    proc_name = decl.name () + '_proc'
    proc_decl = z3.Function (proc_name, *proc_sorts)

    # update decls
    decls [proc_name] = proc_decl
    del decls [name]

    # factor the self-loop out into a procedure;
    # can have multiple self-loop rules because of the transformation

    # Self loop: P(x) /\ t(x,x') -> P(x')
    # Transformed rule: t(x,x') /\ P_proc(x',x!next) -> P_proc(x,x!next)
    for rule in loop_rules:
        curr_args = [rule.get_body_inst ().arg (i) for i in arg_indices]
        next_args = [z3.Const (arg.decl ().name () + '!next', arg.sort ()) \
                     for arg in curr_args]
        temp_args = [rule.get_head ().arg (i) for i in arg_indices]
        rule_exp = z3.ForAll (rule.qvars + next_args,
                              z3.Implies (z3.And (proc_decl (*(temp_args + next_args)),
                                                  rule.get_trans ()),
                                          proc_decl (*(curr_args + next_args))))
        print 'Removing loop rule', repr (rule)
        rules.remove (rule)
        rules.append (Rule (rule_exp))

    # Exit rule: P(x) /\ t(x,y) -> Q(y)
    # Exit rule of P_proc: t(x,y) -> P_proc (x,x)
    for rule in succs [name]:
        curr_args = [rule.get_body_inst ().arg (i) for i in arg_indices]
        next_args = curr_args
        rule_exp = z3.ForAll (rule.qvars,
                              z3.Implies (rule.get_trans (),
                                          proc_decl (*(curr_args + next_args))))
        rules.append (Rule (rule_exp))

    # wire incoming and outgoing rules, via P, together
    # in-rule: Q(y) /\ t(y,x) -> P(x)
    # out-rule: P(x) /\ t(x,z) -> R(z)
    # new rule: Q(y) /\ t(y,x) /\ P_proc (x,x') /\ t(x',z) -> R(z)
    for in_rule in preds [name]:
        #print 'In rule:', repr (in_rule)
        if in_rule.has_body_pred ():
            from_inst = in_rule.get_body_inst ()
        else:
            from_inst = z3.BoolVal (True)
        in_trans = in_rule.get_trans ()
        curr_args = [in_rule.get_head ().arg (i) for i in arg_indices]

        for out_rule in succs [name]:
            #print 'Out rule:', repr (out_rule)

            # version all out_rule.qvars; treat body args and the rest separately
            sub = list ()
            out_vars = list ()
            # body args
            for i in range (decl.arity ()):
                v = out_rule.get_body_inst ().arg (i)
                if i in arg_indices:
                    # create new variable
                    v_new = z3.Const (v.decl ().name () + '_temp', v.sort ())
                    out_vars.append (v_new)
                else:
                    # use corresponding arg from in_rule; it is unchanged by the loop
                    v_new = in_rule.get_head ().arg (i)
                sub.append ( (v,v_new) )
            # rest
            for v in out_rule.qvars:
                is_body_arg = False
                for i in range (decl.arity ()):
                    if z3.eq (v, out_rule.get_body_inst ().arg (i)):
                        is_body_arg = True
                        break
                if is_body_arg: continue

                v_temp = z3.Const (v.decl ().name () + '_temp', v.sort ())
                sub.append ( (v,v_temp) )
                out_vars.append (v_temp)

            next_args = [z3.substitute (out_rule.get_body_inst ().arg (i), *sub)\
                         for i in arg_indices]
            out_trans = z3.substitute (out_rule.get_trans (), *sub)
            to_inst = z3.substitute (out_rule.get_head (), *sub)

            # make new rule via proc_decl
            rule_exp = z3.ForAll (in_rule.qvars + out_vars,
                                  z3.Implies (z3.And (from_inst,
                                                      in_trans,
                                                      proc_decl (*(curr_args + next_args)),
                                                      out_trans),
                                              to_inst))
            rule = Rule (rule_exp)
            if rule.is_self_loop ():
                insert_in_dict (self_loops, rule.get_head_pred_name (), rule)
            else:
                insert_in_dict (preds, rule.get_head_pred_name (), rule)
                if rule.has_body_pred ():
                    insert_in_dict (succs, rule.get_body_pred_name (), rule)
            rules.append (rule)

    # remove incoming and outgoing rules, via P
    for in_rule in preds [name]:
        print 'Removing in rule', repr (in_rule)
        rules.remove (in_rule)
        if in_rule.has_body_pred ():
            remove_from_dict (succs, in_rule.get_body_pred_name (), in_rule)
    del preds [name]
    for out_rule in succs [name]:
        print 'Removing out rule', repr (out_rule)
        rules.remove (out_rule)
        remove_from_dict (preds, out_rule.get_head_pred_name (), out_rule)
    del succs [name]


def output (decls, rules, ctx, q, filename):
    fp = z3.Fixedpoint (ctx=ctx)
    fp.set (slice=False)
    fp.set (inline_linear=False)
    fp.set (inline_eager=False)
    for name,decl in decls.iteritems ():
        fp.register_relation (decl)
    for r in rules:
        fp.add_rule (r.rule_exp)

    if filename is None:
        f = sys.stdout
    else:
        f = open (filename, 'w')
    f.write (repr (fp))
    f.write ('(query {})\n'.format (q [0]))


def main (argv):
    args = parseArgs (argv[1:])

    ctx = z3.Context ()
    fp = z3.Fixedpoint (ctx=ctx)
    fp.set (slice=False)
    fp.set (inline_linear=False)
    fp.set (inline_eager=False)

    q = fp.parse_file (args.file)

    decls = dict ()
    rules = list ()
    self_loops = dict ()
    preds = dict ()
    succs = dict ()

    parse (fp, decls, rules, self_loops, preds, succs)

    print 'After parsing:'

    print 'Rules:'
    for r in rules:
        print repr (r)

    print '\nSelf Loops:'
    for key,val in self_loops.iteritems ():
        print key, ': ',
        for r in val:
            print repr (r), ',',
        print

    print '\nPreds:'
    for key,val in preds.iteritems ():
        print key, ': ',
        for r in val:
            print repr (r), ',',
        print

    print '\nSuccs:'
    for key,val in succs.iteritems ():
        print key, ': ',
        for r in val:
            print repr (r), ',',
        print
    print

    # find init pred
    init_pred_name = None
    for key,val in preds.iteritems ():
        for rule in val:
            if not rule.has_body_pred ():
                init_pred_name = key
                break
        if init_pred_name is not None:
            break
    assert init_pred_name is not None

    # get dfs numbering
    numbers = dfs_number (decls, init_pred_name, succs)
    # outline loops in reverse order of dfs numbers
    names = sorted (numbers.keys (), key=lambda n: numbers [n], reverse=True)
    print 'Dfs ordering (reverse):', names, '\n'
    for name in names:
        if name not in self_loops: continue
        print 'Factoring out loop on:', name
        outline_loop (name, decls, rules, self_loops, preds, succs)
        print

    #print 'Rule Exps:'
    #for r in rules:
        #print repr (r.rule_exp)

    output (decls, rules, fp.ctx, q, args.out)


if __name__ == '__main__':
    res = main (sys.argv)
    sys.exit (res)
