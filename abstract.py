import murphi

class DontCareExpr(murphi.MurphiExpr):
    """Unknown expression in Murphi"""
    def __init__(self):
        pass

    def priority(self):
        return 100

    def __str__(self):
        return "DontCare"

    def __repr__(self):
        return "DontCareExpr()"

def safeVar(e, limits):
    """Check safe condition on variable."""
    if isinstance(e, murphi.VarExpr):
        return True
    elif isinstance(e, murphi.FieldName):
        return True
    elif isinstance(e, murphi.ArrayIndex):
        if not isinstance(e.idx, murphi.VarExpr) or e.idx.name not in limits:
            raise NotImplementedError("safeVar on %s" % e)
        return limits[e.idx.name]
    else:
        raise NotImplementedError("safeVar on %s" % e)

def safeExp(e, limits):
    """Check safe condition on expressions."""
    if isinstance(e, murphi.BooleanExpr):
        return True
    elif isinstance(e, murphi.EnumValExpr):
        return True
    elif isinstance(e, murphi.VarExpr):
        if isinstance(e.typ, murphi.VarType):
            if e.typ.name == "NODE":
                if e.name not in limits:
                    raise NotImplementedError("safeExp on %s" % e)
                return limits[e.name]
            else:
                return True
        elif isinstance(e.typ, murphi.BooleanType):
            return safeVar(e, limits)
        elif isinstance(e.typ, murphi.EnumType):
            return safeVar(e, limits)
        else:
            raise NotImplementedError("safeExp on %s" % e)
    elif isinstance(e, murphi.FieldName):
        return True
    elif isinstance(e, murphi.ArrayIndex):
        return safeVar(e, limits)
    else:
        raise NotImplementedError("safeExp on %s" % e)

def safeForm(e, limits):
    """Check safe condition on formulas."""
    if isinstance(e, murphi.OpExpr):
        if e.op in ('=', '!='):
            return safeExp(e.expr1, limits) and safeExp(e.expr2, limits)
        elif e.op in ('&', '|', '->'):
            return safeForm(e.expr1, limits) and safeForm(e.expr2, limits)
        else:
            raise NotImplementedError("safeForm on %s" % e)
    elif isinstance(e, murphi.NegExpr):
        return safeForm(e.expr, limits)
    elif isinstance(e, murphi.ForallExpr):
        return False
    elif isinstance(e, (murphi.BooleanExpr, murphi.VarExpr, murphi.FieldName, murphi.ArrayIndex)):
        return safeExp(e, limits)
    else:
        raise NotImplementedError("safeForm on %s" % e)

def boundVar(e, i):
    """Check bound condition on variables."""
    if isinstance(e, murphi.VarExpr):
        return True
    elif isinstance(e, murphi.FieldName):
        return True
    elif isinstance(e, murphi.ArrayIndex):
        return isinstance(e.idx, murphi.VarExpr) and e.idx.name == i
    else:
        raise NotImplementedError("boundVar on %s" % e)

def boundExp(e, i):
    """Check bound condition on expressions."""
    if isinstance(e, murphi.BooleanExpr):
        return True
    elif isinstance(e, murphi.EnumValExpr):
        return True
    elif isinstance(e, murphi.VarExpr):
        if isinstance(e.typ, murphi.VarType) and e.typ.name == "NODE":
            return e.name == i
        elif isinstance(e.typ, murphi.BooleanType):
            return boundVar(e, i)
        elif isinstance(e.typ, murphi.EnumType):
            return boundVar(e, i)
        else:
            raise NotImplementedError("boundExp on %s" % e)
    elif isinstance(e, murphi.FieldName):
        return True
    elif isinstance(e, murphi.ArrayIndex):
        return boundVar(e, i)
    else:
        raise NotImplementedError("boundExp on %s" % e)

def boundForm(e, i):
    """Check bound condition on formulas."""
    if isinstance(e, murphi.OpExpr):
        if e.op in ('=', '!='):
            return boundVar(e.expr1, i) and boundExp(e.expr2, i)
        elif e.op in ('&', '|', '->'):
            return boundForm(e.expr1, i) and boundForm(e.expr2, i)
        else:
            raise NotImplementedError("boundForm on %s" % e)
    elif isinstance(e, murphi.NegExpr):
        return boundForm(e.expr, i)
    elif isinstance(e, murphi.ForallExpr):
        return False
    elif isinstance(e, (murphi.BooleanExpr, murphi.VarExpr, murphi.FieldName, murphi.ArrayIndex)):
        return boundExp(e, i)
    else:
        raise NotImplementedError("boundForm on %s" % e)

def boundStatement(cmd, i):
    """Check bound condition on statements."""
    if isinstance(cmd, murphi.Skip):
        return True
    elif isinstance(cmd, murphi.AssignCmd):
        if isinstance(cmd.expr, murphi.OpExpr):
            return boundVar(cmd.var, i) and boundForm(cmd.expr, i)
        else:
            return boundVar(cmd.var, i) and boundExp(cmd.expr, i)
    elif isinstance(cmd, murphi.IfCmd):
        for cond, cmds in cmd.if_branches:
            if not boundForm(cond, i):
                return False
            if not all(boundStatement(c, i) for c in cmds):
                return False
        if cmd.else_branch:
            if not all(boundStatement(c, i) for c in cmd.else_branch):
                return False
        return True
    elif isinstance(cmd, murphi.ForallCmd):
        return False
    else:
        return NotImplementedError("boundStatement on %s" % cmd)

def absTransfConst(e, limits):
    """Abstraction of a constant."""
    if isinstance(e, murphi.BooleanExpr):
        return e
    elif isinstance(e, murphi.EnumValExpr):
        return e
    elif isinstance(e, murphi.VarExpr):
        if isinstance(e.typ, murphi.VarType) and e.typ.name == "NODE":
            if limits[e.name]:
                return e
            else:
                return murphi.EnumValExpr(murphi.EnumType(["Other"]), "Other")
        else:
            raise NotImplementedError("absTransfConst on %s" % e)
    else:
        raise NotImplementedError("absTransfConst on %s" % e)

def absTransfVar(e, limits):
    """Abstraction of a variable."""
    if isinstance(e, murphi.VarExpr):
        if isinstance(e.typ, murphi.VarType) and e.typ.name == "NODE":
            return absTransfConst(e, limits)
        else:
            return e
    elif isinstance(e, murphi.FieldName):
        abs_v = absTransfVar(e.v, limits)
        if isinstance(abs_v, DontCareExpr):
            return DontCareExpr()
        else:
            return murphi.FieldName(abs_v, e.field)
    elif isinstance(e, murphi.ArrayIndex):
        if not isinstance(e.idx, murphi.VarExpr) or e.idx.name not in limits:
            raise NotImplementedError("absTransfVar on %s" % e)
        if limits[e.idx.name]:
            return e
        else:
            return DontCareExpr()
    elif isinstance(e, DontCareExpr):
        return DontCareExpr()
    else:
        raise NotImplementedError("absTransfVar on %s" % e)

def absTransfExp(e, limits):
    """Abstraction of an expression."""
    if isinstance(e, murphi.BooleanExpr):
        return absTransfConst(e, limits)
    elif isinstance(e, murphi.EnumValExpr):
        return absTransfConst(e, limits)
    elif isinstance(e, murphi.VarExpr):
        return absTransfVar(e, limits)
    elif isinstance(e, murphi.FieldName):
        return absTransfVar(e, limits)
    elif isinstance(e, murphi.ArrayIndex):
        return absTransfVar(e, limits)
    elif isinstance(e, DontCareExpr()):
        return DontCareExpr()
    else:
        raise NotImplementedError("absTransfExp on %s" % e)

def check_forall_exclude_form(e):
    """If e is of the form forall j : NODE do j != i -> P, return (i, P).
    Otherwise, return None.
    
    """
    if isinstance(e, murphi.ForallExpr):
        if is_imp(e.expr):
            assm, concl = e.expr.expr1, e.expr.expr2
            if assm.op == '!=' and assm.expr1.name == e.var and isinstance(assm.expr2, murphi.VarExpr):
                return assm.expr2.name, concl

def absTransfForm(e, limits):
    """Abstraction of a formula."""
    if isinstance(e, murphi.OpExpr):
        if e.op == '=':
            abs_e1, abs_e2 = absTransfExp(e.expr1, limits), absTransfExp(e.expr2, limits)
            if isinstance(abs_e1, DontCareExpr) or isinstance(abs_e2, DontCareExpr):
                return DontCareExpr()
            else:
                return murphi.OpExpr(e.op, abs_e1, abs_e2)
        elif e.op == '!=':
            abs_e1, abs_e2 = absTransfExp(e.expr1, limits), absTransfExp(e.expr2, limits)
            if isinstance(abs_e1, DontCareExpr) or isinstance(abs_e2, DontCareExpr) or \
                not safeForm(murphi.OpExpr('=', e.expr1, e.expr2), limits):
                return DontCareExpr()
            else:
                return murphi.OpExpr(e.op, abs_e1, abs_e2)
        elif e.op == '&':
            abs_e1, abs_e2 = absTransfForm(e.expr1, limits), absTransfForm(e.expr2, limits)
            if isinstance(abs_e1, DontCareExpr):
                return abs_e2
            elif isinstance(abs_e2, DontCareExpr):
                return abs_e1
            else:
                return murphi.OpExpr(e.op, abs_e1, abs_e2)
        elif e.op == '|':
            abs_e1, abs_e2 = absTransfForm(e.expr1, limits), absTransfForm(e.expr2, limits)
            if isinstance(abs_e1, DontCareExpr) or isinstance(abs_e2, DontCareExpr):
                return DontCareExpr()
            else:
                return murphi.OpExpr(e.op, abs_e1, abs_e2)
        elif e.op == '->':
            abs_e1, abs_e2 = absTransfForm(e.expr1, limits), absTransfForm(e.expr2, limits)
            if isinstance(abs_e1, DontCareExpr) or isinstance(abs_e2, DontCareExpr) or \
                not safeForm(e.expr1, limits):
                return DontCareExpr()
            else:
                return murphi.OpExpr(e.op, abs_e1, abs_e2)
        else:
            raise NotImplementedError("absTransfForm on %s" % e)
    elif isinstance(e, murphi.NegExpr):
        abs_e = absTransfForm(e.expr, limits)
        if isinstance(abs_e, DontCareExpr) or not safeForm(e, limits):
            return DontCareExpr()
        else:
            return murphi.NegExpr(abs_e)
    elif isinstance(e, murphi.ForallExpr):
        # First, check for ForallExcl case
        excl_form = check_forall_exclude_form(e)
        if excl_form:
            excl_var, concl = excl_form
            if excl_var in limits and boundForm(concl, e.var):
                if limits[excl_var]:
                    return e
                else:
                    return murphi.ForallExpr(e.var_decl, concl)
            else:
                return DontCareExpr()
        elif boundForm(e.expr, e.var):
            return e
        else:
            return DontCareExpr()
    elif isinstance(e, (murphi.BooleanExpr, murphi.VarExpr, murphi.FieldName, murphi.ArrayIndex)):
        return absTransfExp(e, limits)
    else:
        raise NotImplementedError("absTransfForm on %s" % e)

def check_forall_exclude_cmd(c):
    """If c is of the form for j : NODE do if (j != i) then S end, return (i, S).
    Otherwise, return None.
    
    """
    if isinstance(c, murphi.ForallCmd):
        # print(c.cmds, len(c.cmds), c.cmds[0].args)
        if len(c.cmds) == 1 and isinstance(c.cmds[0], murphi.IfCmd) and len(c.cmds[0].args) == 2:
            cond, cmds = c.cmds[0].args
            if cond.op == '!=' and cond.expr1.name == c.var and isinstance(cond.expr2, murphi.VarExpr):
                return cond.expr2.name, cmds

def absTransfStatement(cmd, limits):
    """Abstraction of a statement."""
    if isinstance(cmd, murphi.Skip):
        return cmd
    elif isinstance(cmd, murphi.AssignCmd):
        abs_var = absTransfVar(cmd.var, limits)
        if isinstance(abs_var, DontCareExpr):
            return murphi.Skip()
        else:
            return murphi.AssignCmd(abs_var, absTransfExp(cmd.expr, limits))
    elif isinstance(cmd, murphi.ForallCmd):
        # First, check for ForallExcl case
        res = check_forall_exclude_cmd(cmd)
        if res:
            excl_var, S = res
            if excl_var in limits and all(boundStatement(c, cmd.var) for c in S):
                if limits[excl_var]:
                    return cmd
                else:
                    return murphi.ForallCmd(cmd.var_decl, S)
            else:
                raise NotImplementedError
        elif not all(boundStatement(c, cmd.var) for c in cmd.cmds):
            raise NotImplementedError
        else:
            return cmd
    elif isinstance(cmd, murphi.IfCmd):
        # If reached this point, all if conditions must be safe.
        new_args = []
        found_cmd = False
        for cond, cmds in cmd.if_branches:
            if not safeForm(cond, limits):
                raise NotImplementedError
            new_args.append(absTransfForm(cond, limits))
            new_args.append(absTransfStatements(cmds, limits))
            if new_args[-1]:
                found_cmd = True
        if cmd.else_branch:
            new_args.append(absTransfStatements(cmd.else_branch, limits))
            if new_args[-1]:
                found_cmd = True
        if not found_cmd:
            return murphi.Skip()
        else:
            return murphi.IfCmd(new_args)
    elif isinstance(cmd, murphi.UndefineCmd):
        abs_v = absTransfVar(cmd.var, limits)
        if isinstance(abs_v, DontCareExpr):
            return murphi.Skip()
        else:
            return murphi.UndefineCmd(abs_v)
    else:
        raise NotImplementedError("absTransfStatement on %s" % cmd)

def absTransfStatements(cmds, limits):
    """Abstraction of a list of statements."""
    res = []
    for cmd in cmds:
        abs_cmd = absTransfStatement(cmd, limits)
        if not isinstance(abs_cmd, murphi.Skip):
            res.append(abs_cmd)
    return res

def topTransfForm(e, limits):
    """Top-level abstraction transform"""
    f = absTransfForm(e, limits)
    if isinstance(f, DontCareExpr):
        return murphi.BooleanExpr(True)
    else:
        return f

def absTransfRule(rule, limits, suffix=""):
    """Abstraction of a rule."""
    abs_cond = topTransfForm(rule.cond, limits)
    abs_cmds = absTransfStatements(rule.cmds, limits)
    if len(abs_cmds) == 0:
        return None
    else:
        abs_name = "ABS_" + rule.name + suffix
        return murphi.MurphiRule(abs_name, abs_cond, abs_cmds)

def is_conj(e):
    return isinstance(e, murphi.OpExpr) and e.op == '&'

def split_conj(e):
    if is_conj(e):
        return [e.expr1] + split_conj(e.expr2)
    else:
        return [e]

def list_conj(es):
    assert len(es) > 0
    if len(es) == 1:
        return es[0]
    else:
        return murphi.OpExpr('&', es[0], list_conj(es[1:]))

def is_imp(e):
    return isinstance(e, murphi.OpExpr) and e.op == '->'

def destruct_lemma(lemma: murphi.MurphiExpr):
    if isinstance(lemma, murphi.ForallExpr):
        decls, assms, concls = destruct_lemma(lemma.expr)
        return [lemma.var_decl] + decls, assms, concls
    elif is_imp(lemma):
        return [], split_conj(lemma.expr1), lemma.expr2

def strengthen(rule: murphi.MurphiRule, lemma: murphi.MurphiExpr):
    """Strengthening procedure."""
    _, _, concl = destruct_lemma(lemma)
    cond_assms = split_conj(rule.cond)
    new_cond = list_conj(cond_assms + [concl])
    return murphi.MurphiRule(rule.name, new_cond, rule.cmds)
