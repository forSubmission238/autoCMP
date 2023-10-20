import json
import murphi
import murphiparser as parser
import re
import os
import copy
import argparse

from analyser import inv_strengthen

class DontCareExpr(murphi.BaseExpr):
    def __init__(self):
        pass

    def priority(self):
        return 100

    def __str__(self):
        return "DontCare"

    def __repr__(self):
        return "DontCareExpr()"

def safeVar(e, limits):
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
    if isinstance(e, murphi.VarExpr):
        return True
    elif isinstance(e, murphi.FieldName):
        return True
    elif isinstance(e, murphi.ArrayIndex):
        return isinstance(e.idx, murphi.VarExpr) and e.idx.name == i
    else:
        raise NotImplementedError("boundVar on %s" % e)

def boundExp(e, i):
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
    res = []
    for cmd in cmds:
        abs_cmd = absTransfStatement(cmd, limits)
        if not isinstance(abs_cmd, murphi.Skip):
            res.append(abs_cmd)
    return res

def topTransfForm(e, limits):
    f = absTransfForm(e, limits)
    if isinstance(f, DontCareExpr):
        return murphi.BooleanExpr(True)
    else:
        return f

def absTransfRule(rule, limits, suffix=""):
    # print(rule.name, limits)
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

def destruct_lemma(lemma):
    if isinstance(lemma, murphi.ForallExpr):
        decls, assms, concls = destruct_lemma(lemma.expr)
        return [lemma.var_decl] + decls, assms, concls
    elif is_imp(lemma):
        return [], split_conj(lemma.expr1), lemma.expr2

def strengthen(rule, lemma):
    _, assms, concl = destruct_lemma(lemma)
    cond_assms = split_conj(rule.cond)
    new_cond = list_conj(cond_assms + [concl])
    return murphi.MurphiRule(rule.name, new_cond, rule.cmds)

def test_abstract(filename, spec_filename, output_filename=None):
    prot = parser.parse_file(filename)

    if output_filename:
        with open(output_filename, "w") as f:
            f.write(str(prot))

    with open(spec_filename, "r") as spec:
        spec_data = json.load(spec)

    for test_case in spec_data:
        # Obtain rule and limits
        if 'rule' in test_case:
            print("Testing rule %s" % test_case['rule'])
            rule = prot.rule_map[test_case['rule']]
            limits = dict()
        elif 'ruleset' in test_case:
            print("Testing ruleset %s, limits = %s" % (test_case['ruleset'], test_case['limits']))
            rule = prot.rule_map[test_case['ruleset']].rule
            limits = test_case['limits']
        else:
            continue
        
        ori_rule = rule
        # Strengthen rule if necessary
        if 'strengthen' in test_case:
            for lemma_name in test_case['strengthen']:
                print("lemma_map = {}".format(prot.lemma_map))
                if lemma_name not in prot.lemma_map:
                    print("Strengthening lemma %s not found" % lemma_name)
                    raise AssertionError
                print("###\nlemma's inv is :\n{}\n###".format(prot.lemma_map[lemma_name].inv))
                rule = strengthen(rule, prot.lemma_map[lemma_name].inv)
                print("strengthen Rule is {}".format(rule))

        # Abstract rule
        suffix = "" if 'suffix' not in test_case else test_case['suffix']
        abs_rule = absTransfRule(rule, limits, suffix=suffix)
        print("ABS Rule is {}".format(abs_rule))

        # Check results
        if test_case['answer'] == 'SAME':
            if abs_rule.cond != rule.cond or abs_rule.cmds != rule.cmds:
                print("Found difference. Rule is\n\n%s\n\nAbs rule is\n%s\n" % (ori_rule, abs_rule))
                raise AssertionError
        elif test_case['answer'] == 'NONE':
            if abs_rule is not None:
                print("Expect None. Rule is\n\n%s\n\nAbs rule is\n%s\n" % (ori_rule, abs_rule))
                raise AssertionError
        else:
            abs_rule_name = test_case['answer']
            if abs_rule_name not in prot.rule_map:
                print("Comparison abstract rule %s not found" % abs_rule_name)
                raise AssertionError
            if isinstance(prot.rule_map[abs_rule_name], murphi.MurphiRuleSet):
                exp_rule = prot.rule_map[abs_rule_name].rule
            elif isinstance(prot.rule_map[abs_rule_name], murphi.MurphiRule):
                exp_rule = prot.rule_map[abs_rule_name]
            else:
                raise AssertionError
            if abs_rule != exp_rule:
                print("Found difference. Rule is\n\n%s\n\nAbs rule is\n\n%s\n\nExpected rule is\n\n%s\n" % \
                    (ori_rule, abs_rule, exp_rule))
                raise AssertionError

def initAbs(filename,  output_filename=None):
    prot = parser.parse_file(filename)
    # print(prot)
    suffix=''
    prot.abs_rule_map=dict()
    for k,r in prot.rule_map.items():
        if isinstance(r,murphi.MurphiRuleSet):
            limits=dict()
            if len(r.var_decls)==1:
                limits[r.var_decls[0].name]=False
                absr=absTransfRule(r.rule, limits, suffix=suffix)
                if absr!=r.rule and absr!=None:
                    prot.abs_rule_map[absr.name]=absr
                    prot.decls.append(absr)

            elif len(r.var_decls)==2:
                limits[r.var_decls[0].name]=False
                limits[r.var_decls[1].name]=True
                absr=absTransfRule(r.rule, limits, suffix=suffix)
                absrulesetdecls=r.var_decls[1:2]
                if absr!=r.rule and absr!=None:
                    absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                    prot.abs_rule_map[absr.name]=absruleset
                    prot.decls.append(absruleset)

                limits=dict()
                limits[r.var_decls[1].name]=False
                limits[r.var_decls[0].name]=True
                absr=absTransfRule(r.rule, limits, suffix=suffix)
                absrulesetdecls=r.var_decls[0:1]
                if absr!=r.rule and absr!=None:
                    absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                    prot.abs_rule_map[absr.name]=absruleset
                    prot.decls.append(absruleset)

                limits=dict()
                limits[r.var_decls[0].name]=False
                limits[r.var_decls[1].name]=False
                absr=absTransfRule(r.rule, limits, suffix=suffix)
                if absr!=r.rule and absr!=None:
                    prot.abs_rule_map[absr.name]=absr
                    prot.decls.append(absr)
        else:
             continue      

    if output_filename:
        with open(output_filename, "w") as f:
            f.write(str(prot))

def absStrenthfRule(rule, limits, suffix=""):
    abs_cond = topTransfForm(rule.cond, limits)
    abs_cmds = absTransfStatements(rule.cmds, limits)
    if len(abs_cmds) == 0:
        return None
    else:
        abs_name = rule.name + suffix
        return murphi.MurphiRule(abs_name, abs_cond, abs_cmds)

def abs_strengthen(filename,  output_filename=None, rulename = ''):   
    print("you wanna reading \"{}\"".format(filename)) 
    # print("forall_expr is {}".format(forall_info))
    prot = parser.parse_file(filename)
    # print(prot)
    suffix=''
    absffix='ABS_'
    ori_abs_map = copy.deepcopy(prot.abs_rule_map)
    for k,r in ori_abs_map.items():
        if isinstance(r,murphi.MurphiRuleSet) and str(k) == rulename:
            limits=dict()
            if len(r.var_decls)==1:
                limits[r.var_decls[0].name]=False
                prot.decls.remove(prot.abs_rule_map[r.rule.name])
                absr=absStrenthfRule(r.rule, limits, suffix=suffix)
                # print(absr)
                if absr!=None and absr != r:
                    prot.decls.append(absr)
                    prot.abs_rule_map.update({absr.name:absr})

            elif len(r.var_decls)==2:
                ori_r = r
                result = []
                prot.decls.remove(prot.abs_rule_map[r.rule.name])
                del(prot.abs_rule_map[r.rule.name])
                limits[ori_r.var_decls[0].name]=False
                limits[ori_r.var_decls[1].name]=True
                suffix = '_{}'.format(str(ori_r.var_decls[0].name))
                absr=absStrenthfRule(ori_r.rule, limits, suffix=suffix)
                absrulesetdecls=r.var_decls[1:2]
                if absr!=None and absr != r:
                    absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                    prot.abs_rule_map.update({absr.name:absr})
                    prot.decls.append(absruleset)            

                limits=dict()
                limits[ori_r.var_decls[1].name]=False
                limits[ori_r.var_decls[0].name]=True
                suffix = '_{}'.format(str(ori_r.var_decls[1].name))
                absr=absStrenthfRule(ori_r.rule, limits, suffix=suffix)
                absrulesetdecls=ori_r.var_decls[0:1]
                if absr!=None and absr != r:
                    absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                    prot.abs_rule_map.update({absr.name:absr})
                    prot.decls.append(absruleset)

                limits=dict()
                limits[r.var_decls[0].name]=False
                limits[r.var_decls[1].name]=False
                suffix = '_{}_{}'.format(str(ori_r.var_decls[0].name), str(ori_r.var_decls[1].name))
                absr=absStrenthfRule(ori_r.rule, limits, suffix=suffix)
                if absr!=None and absr != r:
                    prot.decls.append(absr)
                    prot.abs_rule_map.update({absr.name:absr})
                

        else:
             continue      
    
    # print(str(prot))
    if output_filename:
        with open(output_filename, "w") as f:
            f.write(str(prot))


def test_abs_str(flag, name, lemmas):
    #基本设置
    data_dir = '.'
    protocol_name = name
    #读取已有的化简过的rule
    string_list = []
    rulefile = ''
    for lemma in lemmas:
        print("reading {}".format(lemma))
        with open('./{}/useful_rule/{}.txt'.format(protocol_name,lemma), 'r') as f:
            rulefile = f.read()
        string_list.append(rulefile)
    assert len(string_list) != 0
    print("read success!, useful_rules'len : {}".format(len(string_list)))
    rest_string_list = string_list
    if os.path.exists('./ABS{0}.m'.format(protocol_name)):
        with open('./ABS{0}.m'.format(protocol_name), 'r') as f:
            text = f.read()
            assert text != ''
    else:
        print('reading ABS_file failed!')
    str_info = ''
    pattern = re.compile(r'ruleset(.*?)do(.*?)endruleset\s*;', re.S)
    rulesets = pattern.findall(text)
    for params, rules_str in rulesets:
        rules = re.findall(r'(rule.*?endrule;)', rules_str, re.S)
        for each_rule in rules:
            rulename = re.findall(r'rule\s*\"(.*?)\"\s*.*?==>.*?begin.*?endrule\s*;', each_rule, re.S)[0]
            if flag == rulename:
                print("rulename is {}".format(rulename))
                # print('rev_dict is {}'.format(rev_dict))
                rules_str = re.sub(rulename, 'ABS_'+rulename, rules_str)
                ruleset = 'ruleset ' + params + ' do\n' + rules_str + '\nendruleset;'
                str_info= inv_strengthen(rest_string_list, ruleset)
                #加强结束
    assert len(rest_string_list) != 0
    assert str_info != ''
    #填入加强结果
    if os.path.exists("ABS{}.m".format(name)):
        with open("ABS{}.m".format(name), 'r') as f:
            protocol = f.read()
        with open("{}/ABS{}.m".format(data_dir, name), 'w') as f:
            protocol_2 = re.sub(r'rule\s*"ABS_%s".*?endrule;'%flag, '', protocol, flags=re.S)
            protocol_3 = re.sub(r'ruleset.*?do\n\nendruleset;', '', protocol_2)
            f.write(protocol_3)
            f.write(str_info+'\n')
        #抽象
        abs_strengthen("{}/ABS{}.m".format(data_dir, name), "{}/ABS{}.m".format(data_dir, name), rulename = 'ABS_{}'.format(flag))

if __name__ == "__main__":
    arg_parser = argparse.ArgumentParser(description='Learning based CMP')
    arg_parser.add_argument('--task', default='mutualEx')
    args = arg_parser.parse_args()
    
    data_dir = '.'
    protocol_name = args.task
    if os.path.exists('./ABS{0}.m'.format(protocol_name)):
        os.remove('./ABS{0}.m'.format(protocol_name))
    if not os.path.exists("./{0}/ABS{0}.m".format(protocol_name)):
        initAbs("./{0}/{0}.m".format(protocol_name), "./{0}/ABS{0}.m".format(protocol_name))
    assert os.path.exists("./{0}/ABS{0}.m".format(protocol_name))
    os.system('cp ./{0}/ABS{0}.m ./'.format(protocol_name))
    if os.path.exists('./ABS{0}.m'.format(protocol_name)):
        with open('./ABS{0}.m'.format(protocol_name), 'r') as f:
            text = f.read()
            assert text != ''
    with open("{}/{}/str_{}.m".format(data_dir, protocol_name, protocol_name), 'w') as f:
        f.write(text)
    #删除已有的加强记录
    if os.path.exists("{}/{}/abs_process.csv".format(data_dir, protocol_name)):
        os.remove("{}/{}/abs_process.csv".format(data_dir, protocol_name))
    
