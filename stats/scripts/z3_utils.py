#!/usr/bin/env python

############################################
#
# Some utility routines for Z3
#
############################################


import z3

I = z3.IntSort ()
B = z3.BoolSort ()


def z3_translate (x, ctx):
  """ A version of z3.AstRef.translate that handles sorts and function declarations correctly"""
  if x.ctx == ctx: return x
  if isinstance (x, z3.BoolSortRef): return z3.BoolSort (ctx=ctx)
  if z3.is_arith_sort (x): 
    if x.is_int (): return z3.IntSort (ctx=ctx)
    else :
      assert x.is_real ()
      return z3.RealSort (ctx=ctx)
  if isinstance (x, z3.FuncDeclRef):
    sorts = [z3_translate (x.domain (i), ctx) for i in range (x.arity ())]
    sorts.append (z3_translate (x.range (), ctx))
    return z3.Function (x.name (), *sorts)
  if ctx is None: return x.translate (ctx=z3.main_ctx ())
  return x.translate (ctx)


def translate_pair_list (l, ctx):
    res = []
    for (a,b) in l:
        new_p = (z3_translate (a, ctx), z3_translate (b, ctx))
        res.append (new_p)
    return res


def mk_true (ctx=None): return z3.BoolVal (True, ctx=ctx)

def mk_false (ctx=None): return z3.BoolVal (False, ctx=ctx)

def mk_int (val, ctx=None): return z3.IntVal (val, ctx=ctx)


def mk_and (args, ctx=None):
    if len (args) == 0: return mk_true (ctx=ctx)
    else: return z3.And (*args)


def create_fp (smt2file,
               ctx=None, pp=False, engine='pdr', validate=False):
    fp = z3.Fixedpoint (ctx=ctx)
    if not pp:
        print 'No pre-processing'
        fp.set (slice=False)
        fp.set (inline_linear=False)
        fp.set (inline_eager=False)

    fp.set (validate_result=validate)
    fp.set (engine=engine, use_farkas=True, generate_proof_trace=False)

    q = fp.parse_file (smt2file)

    return (q, fp)


def create_named_fp (smt2file,
                     ctx=None, pp=False, engine='pdr', validate=False):
    given_fp = z3.Fixedpoint (ctx=ctx)
    q = given_fp.parse_file (smt2file)
    given_preds = get_preds (given_fp)

    fp = z3.Fixedpoint (ctx=ctx)
    rules = dict () # map from names to rules
    if not pp:
        print 'No pre-processing'
        fp.set (slice=False)
        fp.set (inline_linear=False)
        fp.set (inline_eager=False)
    fp.set (validate_result=validate)
    fp.set (engine=engine, use_farkas=True, generate_proof_trace=False)
    for pred in given_preds.itervalues ():
        fp.register_relation (pred)
    for i,rule in enumerate (given_fp.get_rules ()):
        name = 'r'+str(i)
        fp.add_rule (rule, name=name)
        rules [name] = rule
    return (q, fp, rules)


def create_empty_fp (ctx=None, pp=False, engine='pdr', validate=False):
    fp = z3.Fixedpoint (ctx=ctx)
    if not pp:
        fp.set (slice=False)
        fp.set (inline_linear=False)
        fp.set (inline_eager=False)
    fp.set (validate_result=validate)
    fp.set (engine=engine, use_farkas=True, generate_proof_trace=False)
    return fp


def strip_qblock (expr):
    if not z3.is_quantifier (expr): return ([], expr)
    consts = list ()
    for i in reversed (range (expr.num_vars ())):
        v_name = expr.var_name (i)
        v_sort = expr.var_sort (i)
        consts.append (z3.Const (v_name, v_sort))
    matrix = z3.substitute_vars (expr.body (), *consts)
    return (consts, matrix)


def get_preds (fp):
    preds = dict ()
    pred_keys = []
    for rule_exp in fp.get_rules ():
      # rule_exp is a quantified formula representing the rule of the form:
      #     Forall vars. body => head where head is a QF predicate instance
      # obtain the head
      unused_, matrix = strip_qblock (rule_exp)
      if z3.is_app_of (matrix, z3.Z3_OP_IMPLIES): head = matrix.arg (1)
      else: head = matrix

      assert head is not None

      # obtain head_decl
      head_decl = head.decl ()
    
      # ensure head_decl is in preds
      head_key = exp_key (head_decl)
      if head_key in pred_keys: continue
      pred_keys.append (head_key)
      preds [head_decl.name ()] = head_decl

    return preds


def print_lemmas (fp):
    preds = get_preds (fp)
    print
    for pred in preds.itervalues ():
        print 'Lemmas for predicate: ', pred
        n = fp.get_num_levels (pred)
        for i in range (n):
            print '{} : {}'.format (i, fp.get_cover_delta (i, pred))
        print '{} : {}'.format ('oo', fp.get_cover_delta (-1, pred))
        print


def get_level_lemmas (fp, lvl, pred):
    lemmas = []
    for l in range (lvl, fp.get_num_levels (pred) + 1):
        lemmas.append (fp.get_cover_delta (l, pred))
    lemmas.append (fp.get_cover_delta (-1, pred))
    return z3.simplify (z3.And (*lemmas))


# doesn't seem to quite work when new expressions are created -- use z3.eq instead
def exp_key (e): return e.ast.value


def match_exp (exp1, exp2):
    if exp1 is None and exp2 is None: return True
    if exp1 is None and exp2 is not None: return False
    if exp2 is None and exp1 is not None: return False
    return exp_key (exp1) == exp_key (exp2)


# iterator for declarations of arguments of exp
# if arguments contain de-bruijn variables, they are ignored
def arg_decls (exp):
    for i in range (exp.num_args ()) :
        arg = exp.arg (i)
        if z3.is_app (arg): yield arg.decl ()


def has_const (exp, const):
    found = False
    for l in unique_const_leaves (exp):
        if z3.eq (l, const):
            found = True
            break
    return found


# iterator for all equality terms on const;
#
# each pair (t,eq) is such that eq is an equality logically equivalent to (const==t)
# appearing in exp;
#
# to accommodate for alternative representations of the same equality (e.g. const==1
# vs. 1==const) and to avoid repetitions of terms, we return (None,eq) for the
# duplicates (in the above example, we yield (1,const==1) and (None,1==const));
#
# assume that const only appears in simple arithmetic terms and the coefficient
# of const is 1;
#
# assume that no equality term appears in another equality term
# (so, we can't handle "(const==0)==b", "ite (const==0, x, y) == 3", etc.)
def unique_eq_terms_on_const (const, exp, eq_terms=None, done_exp=None):
    def insert (e):
        found = False
        for t in eq_terms:
            if z3.eq (t,e):
                found = True
                break
        if not found:
            eq_terms.append (e)
            return True
        return False


    def process_eq (e1, e2):
        if z3.eq (e1, const):
            ret_val = z3.simplify (e2)
        else:
            assert z3.is_app (e1)
            if not (z3.is_app_of (e1, z3.Z3_OP_ADD) or z3.is_app_of (e1, z3.Z3_OP_SUB)):
                return None
            is_add = z3.is_app_of (e1, z3.Z3_OP_ADD)
            arg0 = e1.arg (0)
            arg1 = e1.arg (1)
            if z3.eq (arg1, const):
                if is_add: ret_val = z3.simplify (e2-arg0)
                else: ret_val = z3.simplify (arg0-e2)
            else:
                if is_add: ret_val = process_eq (arg0, e2-arg1)
                else: ret_val = process_eq (arg0, e2+arg1)
        return ret_val


    if eq_terms is None: eq_terms = []
    if done_exp is None: done_exp = []

    for e in done_exp:
        if e.eq (exp): return # sub-dag is already processed

    if z3.is_eq (exp):
        arg0 = exp.arg (0)
        arg1 = exp.arg (1)
        if has_const (arg1, const):
            arg0,arg1 = arg1,arg0 # swap
        if has_const (arg0, const):
            t = process_eq (arg0, arg1)
            if t is not None:
                if insert (t): yield (t, exp)
                else: yield (None, exp)
    elif z3.is_app (exp):
        for i in range (exp.num_args ()):
            for (t,eq) in unique_eq_terms_on_const (const, exp.arg (i), eq_terms, done_exp):
                yield (t, eq)

    done_exp.append (exp)



def unique_leaves (exp, leaf_keys=None):
    def insert_and_yield (e):
        k = exp_key (e)
        if k not in leaf_keys:
            leaf_keys.append (k)
            yield e

    if leaf_keys is None: leaf_keys = []

    if z3.is_const (exp) and not (z3.is_int_value (exp) or z3.is_rational_value (exp)):
        for leaf in insert_and_yield (exp): yield leaf
    elif z3.is_app (exp):
        for i in range (exp.num_args ()):
            for leaf in unique_leaves (exp.arg (i), leaf_keys): yield leaf
    else:
        assert z3.is_var (exp)
        for leaf in insert_and_yield (exp): yield leaf


def unique_const_leaves (exp):
    for l in unique_leaves (exp):
        if not z3.is_var (l): yield l


def unique_var_leaves (exp):
    for l in unique_leaves (exp):
        if z3.is_var (l): yield l


def exp_has_const_leaf (exp, l):
    for m in unique_const_leaves (exp):
        if l.eq (m): return True
    return False


def unique_selects (exp, sel_keys=None):
    def insert_and_yield (e):
        k = exp_key (e)
        if k not in sel_keys:
            sel_keys.append (k)
            yield e

    if sel_keys is None: sel_keys = []

    # post-order
    if z3.is_app (exp):
        for i in range (exp.num_args ()): # args are the array and the idx
            for sel in unique_selects (exp.arg (i), sel_keys): yield sel
    if z3.is_select (exp):
        for sel in insert_and_yield (exp): yield sel


def extract_consts (exp):
    res = []
    for c in unique_const_leaves (exp):
        res.append (c)
    return res


def mk_const_variant (const, variant):
    name = '{}_{}'.format (const.decl ().name (), variant)
    return z3.Const (name, const.sort ())


def mk_exp_variant_sub (exp, variant):
    sub = []
    for const in unique_const_leaves (exp):
        const_variant = mk_const_variant (const, variant)
        sub.append ( (const, const_variant) )
    return sub


def mk_fresh_args (decl, startswith=''):
    args = []
    for i in range (decl.arity ()):
        name = startswith + str (i)
        sort = decl.domain (i)
        args.append (z3.Const (name, sort))
    return args


# check if fml is sat with given side constraints
def check_sat (fml, side_cons=None):
    s = z3.Solver (ctx=fml.ctx)
    s.add (fml)
    if side_cons is not None:
        for cons in side_cons:
            s.add (cons)
    res = s.check ()
    if res == z3.sat:
        return s.model ()
    else:
        return None


def mk_subst_from_model (m, consts, model_completion=False):
    sub = []
    for const in consts:
        # treat arrays specially due to the else_value
        sort = const.sort ()
        if isinstance (sort, z3.ArraySortRef):
            val_interp = m [const]
            if (val_interp is not None) and isinstance (val_interp, z3.FuncInterp) :
                idx_sort = sort.domain ()
                val_sort = sort.range ()
                val = z3.K(val_sort, val_interp.else_value ())
                for i in range (val_interp.num_entries ()):
                    entry = val_interp.entry (i)
                    val = z3.Store (val, entry.arg_value (0), entry.value ())
            else:
                val = m.eval (const, model_completion=model_completion)
        else:
            val = m.eval (const, model_completion=model_completion)
        sub.append ( (const, val) )
    return sub


def mk_eqs_from_model (m, consts, model_completion=False):
    eqs = []
    for const in consts:
        # treat arrays specially due to the else_value
        sort = const.sort ()
        if isinstance (sort, z3.ArraySortRef):
            val_interp = m [const]
            if (val_interp is not None) and isinstance (val_interp, z3.FuncInterp):
                idx_sort = sort.domain ()
                val_sort = sort.range ()
                val = z3.K(val_sort, val_interp.else_value ())
                for i in range (val_interp.num_entries ()):
                    entry = val_interp.entry (i)
                    val = z3.Store (val, entry.arg_value (0), entry.value ())
            else:
                val = m.eval (const, model_completion=model_completion)
        else:
            val = m.eval (const, model_completion=model_completion)
        eqs.append (const == val)
    return eqs


def qe_array (exp):
    if not z3.is_quantifier (exp): return exp
    is_forall = False
    if exp.is_forall ():
        is_forall = True
        (qvars, matrix) = strip_qblock (exp)
        exp = z3.Exists (qvars, z3.Not (matrix))
    qf_exp = z3.Tactic ('qe-array', ctx=exp.ctx) (exp).as_expr ()
    if is_forall:
        (qvars, matrix) = strip_qblock (qf_exp)
        if len (qvars) > 0:
            res = z3.ForAll (qvars, z3.Not (matrix))
        else:
            res = z3.Not (matrix)
    else:
        res = qf_exp
    return res


def qe_lite (exp):
    if not z3.is_quantifier (exp): return exp
    e = exp
    t = z3.Tactic ('qe-light', ctx=exp.ctx)
    # invoke qe_lite once per quantified variable, for better result
    for i in range (exp.num_vars ()):
        e = t (e).as_expr ()
        if not z3.is_quantifier (e): return e
    if z3.is_quantifier (e):
        # invoke qe_lite for each variable, separately
        (qvars, matrix) = strip_qblock (e)
        for v in qvars:
            if exp.is_forall ():
                matrix = t (z3.ForAll ([v], matrix)).as_expr ()
            else:
                matrix = t (z3.Exists ([v], matrix)).as_expr ()
        e = matrix
    return e


def qe (exp):
    if not z3.is_quantifier (exp): return exp
    return z3.Tactic ('qe', ctx=exp.ctx) (exp).as_expr ()


# qe_lite followed by qe
def full_qe (exp):
    temp = qe_lite (exp)
    return qe (temp)

def qe_sat (exp):
    t = z3.Tactic ('qe-sat', ctx=exp.ctx)
    return t (exp).as_expr ()


def cofactor_term_ite (exp):
    if z3.is_quantifier (exp):
        (qvars, matrix) = strip_qblock (exp)
        matrix = cofactor_term_ite (matrix)
        if exp.is_forall ():
            return z3.ForAll (qvars, matrix)
        else:
            return z3.Exists (qvars, matrix)
    t = z3.Tactic ('cofactor-term-ite', ctx=exp.ctx)
    return t (exp).as_expr ()


def elim_term_ite (exp):
    if z3.is_quantifier (exp):
        (qvars, matrix) = strip_qblock (exp)
        matrix = elim_term_ite (matrix)
        if exp.is_forall ():
            e = z3.ForAll (qvars, matrix)
        else:
            e = z3.Exists (qvars, matrix)
        return e
    pre_consts = extract_consts (exp)
    pre_const_keys = map (exp_key, pre_consts)
    t = z3.Tactic ('elim-term-ite', ctx=exp.ctx)
    e = t (exp).as_expr ()
    # tactic introduces new constants which need to be existentially quantified
    post_consts = extract_consts (e)
    post_const_keys = map (exp_key, post_consts)
    exist_consts = []
    for i in range (len (post_consts)):
        post_key = post_const_keys [i]
        if post_key not in pre_const_keys:
            exist_consts.append (post_consts [i])
    if len (exist_consts) > 0:
        e = z3.Exists (exist_consts, e)
    return qe_lite (e)


# obtain an under-approx of exp (an existentially quantified fml) under the
# constraints 'side_cons' on the free variables;
#
# let exp = Exists (qvars, matrix)
# obtain a model m of qvars consistent with (matrix /\ side_cons)
# the under-approx. is obtained as "matrix [m/qvars]"
#
# this is the weakest under-approx. if side_cons is a point
def under_approx_qe (exp, side_cons=None):
    assert z3.is_quantifier (exp)
    assert not exp.is_forall ()

    (qvars, matrix) = strip_qblock (exp)
    s = z3.Solver (ctx=exp.ctx)
    s.add (matrix)
    if side_cons is not None:
        for c in side_cons: s.add (c)
    res = s.check ()
    if res == z3.unsat: return mk_false (ctx=exp.ctx)
    m = s.model ()
    sub = mk_subst_from_model (m, qvars, model_completion=True)
    return z3.substitute (matrix, *sub)


def nnf (exp):
    t = z3.Tactic ('nnf', ctx=exp.ctx)
    return t (exp).as_expr ()


def is_ite (exp):
    return z3.is_app_of (exp, z3.Z3_OP_ITE)

def is_xor (exp):
    return z3.is_app_of (exp, z3.Z3_OP_XOR)


# rewrite ite as conjunction of implications when it appears as a boolean atom
# (i.e. an atom in the boolean structure of exp)
def elim_bool_ite (exp):
    if z3.is_quantifier (exp):
        (qvars, matrix) = strip_qblock (exp)
        matrix = elim_bool_ite (matrix)
        if exp.is_forall ():
            e = z3.ForAll (qvars, matrix)
        else:
            e = z3.Exists (qvars, matrix)
        return e
    if not z3.is_bool (exp): return exp
    if z3.is_true (exp) or z3.is_false (exp): return exp
    assert z3.is_app (exp)
    decl = exp.decl ()
    args = map (elim_bool_ite, exp.children ())
    # need to worry about And and Or because they can take >2 args and
    # decl(*args) doesn't seem to work with the py interface
    if z3.is_and (exp):
        return z3.And (*args)
    elif z3.is_or (exp):
        return z3.Or (*args)
    elif is_ite (exp):
        impl1 = z3.Implies (args[0], args[1])
        impl2 = z3.Implies (z3.Not (args[0]), args[2])
        return z3.And (impl1, impl2)
    else:
        return decl (*args)


def elim_ite (exp):
    e = cofactor_term_ite (exp)
    e = elim_bool_ite (e)

    # Alternatively, we could have done the following with the caveat that
    # elim_term_ite introduces new existentially quantified variables which can
    # be hard to eliminate by qe_lite

    #e = elim_bool_ite (exp)
    #e = elim_term_ite (e)

    return e


# sampling based method for quant. alternation;
# given_insts is a list of instances for the universals given by the user as a
#   starting point
def solve_exists_forall (exp, given_insts=None, model=False):
    print 'Exists Forall exp:', exp

    assert z3.is_quantifier (exp) and not exp.is_forall ()
    (exist_consts, e) = strip_qblock (exp)

    if not z3.is_quantifier (e):
        # just an smt problem
        m = check_sat (e)
        if m is None:
            return (None, None, None)
        else:
            if model: return (m, None, None)
            sub = mk_subst_from_model (m, exist_consts, model_completion=True)
            return (sub, None, None)
    else:
        assert e.is_forall ()

    (univ_consts, matrix) = strip_qblock (e)

    print 'Exist consts:', exist_consts
    print 'Univ consts:', univ_consts
    print 'Matrix:', matrix

    w_cons = [] # constraints for witness

    # initialize w with given_insts
    if given_insts is not None:
        for inst in given_insts:
            sub = mk_subst_from_model (inst, univ_consts, model_completion=True)
            w_cons.append (z3.substitute (matrix, *sub))

    new_insts = list ()
    witnesses = list ()
    while True:
        print 'Solver for witness:'
        for cons in w_cons: print cons.sexpr ()

        w = z3.Solver (ctx=exp.ctx)
        for cons in w_cons: w.add (cons)
        # obtain witness for instances
        res = w.check ()

        if res == z3.unsat:
            print 'FALSE\n', new_insts
            return (None, new_insts, witnesses)
        m = w.model ()
        witnesses.append (m)
        print 'Model for new witness:\n', m
        sub = mk_subst_from_model (m, exist_consts, model_completion=True)
        print 'New witness:', sub

        # check if the witness is sufficient
        s = z3.Solver (ctx=exp.ctx)
        print 'checking validity of ', z3.substitute (matrix, *sub)
        s.add (z3.Not (z3.substitute (matrix, *sub)))
        print 'Solver for validity:', z3.Not (z3.substitute (matrix, *sub)).sexpr ()
        res = s.check ()
        if res == z3.unsat:
            print 'TRUE\n', sub
            if model: return (m, None, None)
            return (sub, None, None)
        inst = s.model ()
        new_insts.append (inst)
        print 'New instance:\n', inst
        sub = mk_subst_from_model (inst, univ_consts, model_completion=True)
        w_cons.append (z3.substitute (matrix, *sub))


# like above, but looks for counterexamples of increasing size;
# in other words, we solve the negation of the given problem, looking for
# counterexamples of increasing size, similar to BMC
def solve_exists_forall_incremental (exp, model=False):
    print 'Exists Forall exp:', exp

    assert z3.is_quantifier (exp) and not exp.is_forall ()
    (exist_consts, e) = strip_qblock (exp)

    if not z3.is_quantifier (e):
        # just an smt problem
        m = check_sat (e)
        if m is None:
            return (None, None, None)
        else:
            if model: return (m, None, None)
            sub = mk_subst_from_model (m, exist_consts, model_completion=True)
            return (sub, None, None)
    else:
        assert e.is_forall ()

    (univ_consts, matrix) = strip_qblock (e)

    print 'Exist consts:', exist_consts
    print 'Univ consts:', univ_consts
    print 'Matrix:', matrix

    print 'Solving by negating the problem'

    cex_size = 0
    curr_exist_consts = []
    curr_matrix_disjs = []

    for i in range (cex_size):
        sub = []
        for c in univ_consts:
            name = '{}_{}'.format (c.decl ().name (), str (i))
            const = z3.Const (name, c.sort ())
            curr_exist_consts.append (const)
            sub.append ( (c, const) )
        new_disj = z3.substitute (z3.Not (matrix), *sub)
        curr_matrix_disjs.append (new_disj)

    while True:
        print 'CURRENT SIZE:', cex_size+1
        # look for a cex of size 'cex_size'
        # Exists U1,U2,..U_cex_size. Forall E. Not (matrix),
        #   where U and E are univ_consts and exist_consts

        # add a new set of exist consts
        sub = []
        for c in univ_consts:
            name = '{}_{}'.format (c.decl ().name (), str (cex_size))
            const = z3.Const (name, c.sort ())
            curr_exist_consts.append (const)
            sub.append ( (c, const) )
        new_disj = z3.substitute (z3.Not (matrix), *sub)
        curr_matrix_disjs.append (new_disj)
        curr_exp = z3.Exists (curr_exist_consts,
                              z3.ForAll (exist_consts,
                                         z3.Or (*curr_matrix_disjs)))
        (cex_model, witnesses, _unused_insts) = solve_exists_forall (curr_exp, model=True)

        if cex_model is not None:
            print 'FALSE\n', cex_model
            print 'Size:', cex_size+1
            # TODO: split cex_model into list of models for the original set of
            # universal variables
            return (None, cex_model, witnesses)
        else:
            # no cex of current size
            
            # check if any of the witnesses already works
            for m in witnesses:
                w = z3.Solver (ctx=exp.ctx)
                sub = mk_subst_from_model (m, exist_consts, model_completion=True)
                w.add (z3.substitute (z3.Not (matrix), *sub))
                if w.check () == z3.unsat:
                    print 'TRUE\n', sub
                    if model: return (m, None, None)
                    return (sub, None, None)

            # increment size
            cex_size += 1
