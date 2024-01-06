
import json
from typing import Iterable, List

import murphi
import murphiparser
import isabelle
import abstract
from isabelle import Const, Fun, Op, FunType
from isabelle import Definition, IsabelleLemma, IsabelleLemmas

def translateEnum(enum_typ: str, enum: murphi.EnumType):
    res = []
    for name in enum.names:
        res.append(isabelle.enum_def(enum_typ, name))
    return res

def translateAllEnum(prot: murphi.MurphiProtocol, spec_data):
    res = []
    for item in spec_data:
        if "enum_typs" in item:
            enum_typs = item["enum_typs"]
            for enum_typ in enum_typs:
                enum = prot.enum_typ_map[enum_typ]
                res.extend(translateEnum(enum_typ, enum))
    return res

def translateBooleans():
    return [
        Definition("true", isabelle.scalarValueType, isabelle.boolV(True), is_simp=True, is_equiv=True),
        Definition("false", isabelle.scalarValueType, isabelle.boolV(False), is_simp=True, is_equiv=True),
    ]

def destruct_var(e: murphi.MurphiExpr, vars: List[str]):
    if isinstance(e, murphi.VarExpr):
        assert e.name not in vars, "destruct_var: %s not in %s" % (e.name, vars)
        return [e.name], None
    elif isinstance(e, murphi.ArrayIndex):
        names, idx = destruct_var(e.v, vars)
        return names, e.idx.name
    elif isinstance(e, murphi.FieldName):
        names, idx = destruct_var(e.v, vars)
        return names + [e.field], idx
    else:
        print("destruct var on %s" % e)
        raise NotImplementedError

def translateVar(v: murphi.MurphiExpr, vars: List[str]):
    names, idx = destruct_var(v, vars)
    if idx is None:
        return isabelle.Ident(".".join(names))
    else:
        return isabelle.Para(".".join(names), idx)

def translateExp(e: murphi.MurphiExpr, vars: List[str]):
    if isinstance(e, murphi.UnknownExpr):
        raise NotImplementedError
    elif isinstance(e, murphi.BooleanExpr):
        return isabelle.boolE(e.val)
    elif isinstance(e, murphi.EnumValExpr):
        if e.enum_val == "Other":
            return isabelle.other("N")
        else:
            return isabelle.ConstE(e.enum_val)
    elif isinstance(e, murphi.VarExpr) and e.name in vars:
        return isabelle.index(e.name)
    elif isinstance(e, (murphi.VarExpr, murphi.ArrayIndex, murphi.FieldName)):
        return isabelle.IVar(translateVar(e, vars))
    else:
        print("translateExp: %s" % e)
        raise NotImplementedError

def translateIsabelleExp(e: murphi.MurphiExpr, vars: List[str]):
    if isinstance(e, murphi.UnknownExpr):
        raise NotImplementedError
    elif isinstance(e, murphi.BooleanExpr):
        return isabelle.boolE(e.val)
    elif isinstance(e, murphi.EnumValExpr):
        if e.enum_val == "Other":
            return isabelle.other("N")
        else:
            return isabelle.ConstE(e.enum_val)
    elif isinstance(e, murphi.VarExpr) and e.name in vars:
        return isabelle.index(e.name)
    elif isinstance(e, (murphi.VarExpr, murphi.ArrayIndex, murphi.FieldName)):
        return (translateVar(e, vars))
    else:
        print("translateExp: %s" % e)
        raise NotImplementedError

def translateForm(e: murphi.MurphiExpr, vars: List[str]):
    if isinstance(e, murphi.BooleanExpr):
        if e.val:
            return Const("chaos")
        else:
            raise NotImplementedError
    elif isinstance(e, (murphi.VarExpr, murphi.ArrayIndex, murphi.FieldName)):
        return isabelle.eqF(isabelle.IVar(translateVar(e, vars)), isabelle.boolE(True))
    elif isinstance(e, murphi.ForallExpr):
        excl_form = abstract.check_forall_exclude_form(e)
        if excl_form:
            excl_var, concl = excl_form
            assert excl_var in vars
            vars.append(e.var)
            res = isabelle.allExclF(e.var, translateForm(concl, vars), excl_var, "N")
            del vars[-1]
            return res
        else:
            vars.append(e.var)
            res = isabelle.allF(e.var, translateForm(e.expr, vars), "N")
            del vars[-1]
            return res
    elif isinstance(e, murphi.OpExpr):
        if e.op == "=":
            return isabelle.eqF(translateExp(e.expr1, vars), translateExp(e.expr2, vars))
        elif e.op == "!=":
            return isabelle.notF(isabelle.eqF(translateExp(e.expr1, vars), translateExp(e.expr2, vars)))
        elif e.op == "&":
            return isabelle.andF([translateForm(e.expr1, vars), translateForm(e.expr2, vars)])
        elif e.op == "|":
            return isabelle.orF([translateForm(e.expr1, vars), translateForm(e.expr2, vars)])
        elif e.op == "->":
            return isabelle.impF([translateForm(e.expr1, vars), translateForm(e.expr2, vars)])
        elif e.op== "+":
            return isabelle.addE([translateForm(e.expr1, vars), translateForm(e.expr2, vars)])
    elif isinstance(e, murphi.NegExpr):
        if isinstance(e.expr, (murphi.VarExpr, murphi.ArrayIndex, murphi.FieldName)):
            return isabelle.eqF(isabelle.IVar(translateVar(e.expr, vars)), isabelle.boolE(False))
        else:
            return isabelle.notF(translateForm(e.expr, vars))
    else:
        print("translateForm: %s" % e)
        raise NotImplementedError

def hasParamExpr(e: murphi.MurphiExpr):
    if isinstance(e, (murphi.VarExpr, murphi.ArrayIndex, murphi.FieldName)):
        return False
    elif isinstance(e, (murphi.UnknownExpr, murphi.BooleanExpr)):
        return False
    elif isinstance(e, murphi.EnumValExpr):
        return e.enum_val == "Other"
    elif isinstance(e, murphi.ForallExpr):
        return True
    elif isinstance(e, murphi.OpExpr):
        return hasParamExpr(e.expr1) or hasParamExpr(e.expr2)
    elif isinstance(e, murphi.NegExpr):
        return hasParamExpr(e.expr)
    else:
        print("hasParamExpr on %s" % e)
        raise NotImplementedError

def hasParamCmd(cmd: murphi.MurphiCmd):
    if isinstance(cmd, murphi.UndefineCmd):
        return False
    elif isinstance(cmd, murphi.AssignCmd):
        return hasParamExpr(cmd.expr)
    elif isinstance(cmd, murphi.ForallCmd):
        return True
    elif isinstance(cmd, murphi.IfCmd):
        for _, cmds in cmd.if_branches:
            if any(hasParamCmd(c) for c in cmds):
                return True
        if cmd.else_branch and any(hasParamCmd(c) for c in cmd.else_branch):
            return True
        return False
    else:
        print("hasParamCmd on %s" % cmd)
        raise NotImplementedError

def translateVar1(v: murphi.MurphiExpr, vars: List[str]):
    names, idx = destruct_var(v, vars)
    if idx is None:
        return ".".join(names), None
    else:
        return ".".join(names), idx


class initSpec:
    def __init__(self,cmd,vars,order):
        self.cmd=cmd 
        self.vars=vars
        self.order=order
        self.name="initSpec" + str(order)
        (str1,result)=translateVar1(self.cmd.var,vars)
        if not(result is None):
            self.assignVar=(str1)
            self.isGlobal=False 
        else:
            self.assignVar=str1
            self.isGlobal=True

        if isinstance(cmd, murphi.AssignCmd):
            typ = isabelle.formula
            for _ in range(len(vars)):
                typ = FunType(isabelle.nat, typ)
            val = isabelle.eqF(translateExp(cmd.var, vars), translateExp(cmd.expr, vars))
            self.assignVarInIsabelle=translateExp(cmd.var, vars)
            args = []
            assert len(vars) <= 1
            for v in vars:
                val = isabelle.allF(v, val, "N")
                args.append("N")
            self.defi=Definition(self.name, typ, val, args=args, is_simp=True, is_equiv=True)
        elif  isinstance(cmd, murphi.UndefineCmd): 
            def_name = "initSpec" + str(order)
            typ = isabelle.formula
            for _ in range(len(vars)):
                typ = FunType(isabelle.nat, typ)
            assert cmd.var!= "i_0"
            val = isabelle.eqF(translateExp(cmd.var, vars), isabelle.index("i_0") )
            self.assignVarInIsabelle=translateExp(cmd.var, vars)
            args = []
            assert len(vars) <= 1
            for v in vars:
                val = isabelle.allF(v, val, "N")
                args.append("N")
            val=isabelle.exF("i_0",val,"N")
            typ = FunType(isabelle.nat, typ) if vars==[] else typ
            if len(args)==0:
                args.append("N")  
            self.defi=(Definition(self.name, typ, val, args=args, is_simp=True, is_equiv=True))
        

    def genInitSubgoalProof(self):
        args = [Const(arg) for arg in self.defi.args]
        pred = Fun(Const("formEval"), [Fun(Const(self.defi.name), args), Const("s0")])
        return isabelle.subgoaltacProof(pred)

    def __str__(self):
        return self.name + str(self.order) + self.assignVar

def translateStartState(prot: murphi.MurphiProtocol):
    count = 0
    res = []
    opds=[]
    initSpecs=[]
    def translate(cmd, vars):
        nonlocal count
        if isinstance(cmd, murphi.AssignCmd):
            def_name = "initSpec" + str(count)
            count += 1
            typ = isabelle.formula
            for _ in range(len(vars)):
                typ = FunType(isabelle.nat, typ)
            val = isabelle.eqF(translateExp(cmd.var, vars), translateExp(cmd.expr, vars))
            args = []
            assert len(vars) <= 1
            for v in vars:
                val = isabelle.allF(v, val, "N")
                args.append("N")
            res.append(Definition(def_name, typ, val, args=args, is_simp=True, is_equiv=True))
            predic=Const(def_name) if args==[] else  Fun(Const(def_name),[Const("N") ])
            proof=[isabelle.AutoProof()] if args==[] else [isabelle.IsabelleApplyRuleProof(name="symPredSetForall",unfolds=[def_name]),
            isabelle.AutoProof(unfolds=["symParamForm"])]
            lemma = IsabelleLemma(
                [], Fun(Const("symPredSet'"), [Const("N"),isabelle.Set(predic)]),
                attribs=["intro"],
                name="symPreds" + str(count - 1),
                proof=proof)
            res.append(lemma) 
            setOpd = [] if args==[] else [Const("N")]
            opd=isabelle.Set(Fun(Const(def_name), setOpd  ))
            opds.append(opd)
            '''f ∈ {InitSpecs_1 N} ==>deriveForm (env N) f'''
            assm=Op(":",Const("f"),opd)
            proof=isabelle.AutoProof()
            conclusion=Fun(Const("deriveForm"),[Fun(Const("env"),[Const("N")]), Const("f")])
            lemma=IsabelleLemma(assms=[assm],conclusion=conclusion, \
            attribs=["intro"],name="deriveFormInitSpec"+ str(count - 1),proof=[proof])
            res.append(lemma)
            initSpecs.append(initSpec(cmd,vars,count - 1))

        elif isinstance(cmd, murphi.UndefineCmd):
            def_name = "initSpec" + str(count)
            count += 1
            typ = isabelle.formula
            for _ in range(len(vars)):
                typ = FunType(isabelle.nat, typ)
            assert cmd.var!= "i_0"
            val = isabelle.eqF(translateExp(cmd.var, vars), isabelle.index("i_0") )
            args = []
            assert len(vars) <= 1
            for v in vars:
                val = isabelle.allF(v, val, "N")
                args.append("N")
            val=isabelle.exF("i_0",val,"N")
            typ = FunType(isabelle.nat, typ) if vars==[] else typ
            if len(args)==0:
                args.append("N")  
            res.append(Definition(def_name, typ, val, args=args, is_simp=True, is_equiv=True))

            predic=Fun(Const(def_name),[Const("N") ]) #Const(def_name) if args==[] else  
            proof=[isabelle.IsabelleApplyRuleProof(name="symPredSetExist",unfolds=[def_name]),
            isabelle.AutoProof(unfolds=["symParamForm"])] if vars==[] else [isabelle.IsabelleApplyRuleProof(name="symPredSetExistForall",unfolds=[def_name]),
            isabelle.AutoProof(unfolds=["symParamForm2"])]
            lemma = IsabelleLemma(
                [], Fun(Const("symPredSet'"), [Const("N"), isabelle.Set(predic)]),
                attribs=["intro"],
                name="symPreds" + str(count - 1),
                proof=proof)
            res.append(lemma) 

            setOpd = [Const("N")] #[] if args==[] else 
            opd=isabelle.Set(Fun(Const(def_name), setOpd  ))
            opds.append(opd) 
            '''f ∈ {InitSpecs_1 N} ==>deriveForm (env N) f'''
            assm=Op(":",Const("f"),opd)
            conclusion=Fun(Const("deriveForm"),[Fun(Const("env"),[Const("N")]), Const("f")])
            proof=isabelle.AutoProof()
            lemma=IsabelleLemma(assms=[assm],conclusion=conclusion, \
            attribs=["intro"],name="deriveFormInitSpec"+ str(count - 1),proof=[proof])
            res.append(lemma) 
            initSpecs.append(initSpec(cmd,vars,count - 1))

        elif isinstance(cmd, murphi.ForallCmd):
            assert cmd.typ == murphi.VarType("NODE")
            vars.append(cmd.var)
            for c in cmd.cmds:
                translate(c, vars)
            del vars[-1]

        else:
            print("translateStartState: %s" % cmd)
            raise NotImplementedError

    for cmd in prot.start_state.cmds:
        translate(cmd, [])
    
    val=isabelle.UN(opds)
    allSpec=Definition("allInitSpecs", FunType(isabelle.nat, isabelle.setType(isabelle.formula)), val, args=["N"], is_simp=True, is_equiv=True) 
    res.append(allSpec)
    proofs=[]
    for k  in range(len(opds)-1):
        proofs.append(isabelle.IsabelleApplyRuleProof(name="symPredsUnion",unfolds= ["allInitSpecs"]))
        proofs.append(isabelle.blastProof())
    theLast=isabelle.blastProof() if (len(opds)>1) else isabelle.blastProof(unfolds=["allInitSpecs"])
    lemma = IsabelleLemma([], 
        Fun(Const("symPredSet'"), [Const("N"), Fun(Const("allInitSpecs"),[Const("N")])]),
        attribs=["intro"],
        name="symPreds",
        proof=proofs+[theLast]
    )
    res.append(lemma)
    assm=Op(":",Const("f"),Fun(Const("allInitSpecs"), [Const("N")]))
    conclusion=Fun(Const("deriveForm"),[Fun(Const("env"),[Const("N")]), Const("f")])
    
    usings=["deriveFormInitSpec"+str(k) for k in range(0,count )]
    simpdels=["initSpec"+ str(k) +"_def" for k in range(0,count )]
    proof=isabelle.AutoProof(usings=usings,simpdels=simpdels)
    lemma=IsabelleLemma(assms=[assm], conclusion=conclusion, \
        proof=[proof],name="deriveFormAllInitSpec")
    res.append(lemma)
    return (res,initSpecs)

'''def translateEnv(prot):
    eqs=[]
    for var_decl in prot.vars:
        if var_decl.typ
        self.var_map[var_decl.name] = var_decl.typ'''


#generate environment definitions, and lemmas, declarations
def translateEnvByStartState(prot):
    eqIdents=[]
    eqParas=[]
    cmpPara=Fun(Const("Para"),[Const("n"),Const("i")])
    cmpIdent=Fun(Const("Ident"),[Const("n")])
    identLemmas=[]
    paraLemmas=[]
    para=""

    def makeite(isIdentOrPara="isIdent"):
        if isIdentOrPara=="isIdent":
            if(eqIdents!=[]):
                left,right=eqIdents[0]
                del(eqIdents[0])
                eq=isabelle.eq(cmpIdent,left)
                
                return(isabelle.IsabelleITE("isabelleIte",eq,right,makeite("isIdent")))
            else:
                return(Const("anyType"))
        else:
            if(eqParas!=[]):
                left,right=eqParas[0]
                del(eqParas[0])
                eq=isabelle.eq(cmpPara,left)
                eq1=Op("<=",Const(para),Const("N"))
                cond=Op("&",eq,eq1)
                return(isabelle.IsabelleITE("isabelleIte",cond,right,makeite("isPara")))
            else:
                return(Const("anyType"))

    def makeSimpLemmasOn(i,isIdentOrPara="isIdent"):
        if isIdentOrPara=="isIdent":
            if (i==len(eqIdents)):
                pass
            else:
                left,right=eqIdents[i]
                left1=Fun(Const("env"),[Const("N"),left])
                eq=isabelle.eq(left1,right)
                identLemmas.append(IsabelleLemma(assms=[], conclusion=eq,inLemmas=True))
                makeSimpLemmasOn(i+1,"isIdent")
        else:
            if (i==len(eqParas)):
                pass
            else:
                left,right=eqParas[i]
                left2=Fun(Const("env"),[Const("N"),left])
                eq1=isabelle.eq(left2,right)
                cond1=Op("<=",Const(para),Const("N"))
                paraLemmas.append(IsabelleLemma(assms=[cond1], conclusion=eq1,inLemmas=True))
                makeSimpLemmasOn(i+1,"isPara")

    def hasArrayIndex(v: murphi.MurphiExpr) -> bool:
        """Return whether v contains an array index."""
        if isinstance(v, murphi.VarExpr):
            return False
        elif isinstance(v, murphi.ArrayIndex):
            return True
        elif isinstance(v, murphi.FieldName):
            return hasArrayIndex(v.v)
        else:
            raise AssertionError

    def translate(cmd: murphi.MurphiCmd, vars: List[str]):
        nonlocal para
        if isinstance(cmd, murphi.AssignCmd):
            varOpd = translateIsabelleExp(cmd.var, vars)
            typ = Const("enumType") if isinstance(cmd.expr,murphi.EnumValExpr) else \
                  Const("boolType") if isinstance(cmd.expr,murphi.BooleanExpr) else \
                  Const("indexType")
            val = varOpd, typ
            if hasArrayIndex(cmd.var):
                eqParas.append(val)
            else:
                eqIdents.append(val)

        elif isinstance(cmd, murphi.UndefineCmd):
            varOpd = translateIsabelleExp(cmd.var, vars)
            typ = Const("indexType") 
            val = varOpd, typ
            if hasArrayIndex(cmd.var):
                eqParas.append(val)
            else:
                eqIdents.append(val)

        elif isinstance(cmd, murphi.ForallCmd):
            assert cmd.typ == murphi.VarType("NODE")
            vars.append(cmd.var)
            para = cmd.var
            for c in cmd.cmds:
                translate(c, vars)
            del vars[-1]

        else:
            print("translateStartState: %s" % cmd)
            raise NotImplementedError

    for cmd in prot.start_state.cmds:
        translate(cmd, [])

    cmpPara=Fun(Const("Para"),[Const("n"),Const(para)])
    cmpIdent=Fun(Const("Ident"),[Const("n")])
    makeSimpLemmasOn(0,"isIdent")
    makeSimpLemmasOn(0,"isPara")
             
    paraLemmas.extend(identLemmas)  
    
    left2=Fun(Const("env"),[Const("N"),cmpPara])
    eq2=isabelle.eq(left2,Const("anyType"))
    cond2=Op(">",Const(para),Const("N"))
    paraLemmas.append(IsabelleLemma(assms=[cond2], conclusion=eq2,inLemmas=True))
    
    left1=Fun(Const("env"),[Const("N"),cmpIdent])
    eq1=isabelle.eq(left1,makeite("isIdent"))
    left2=Fun(Const("env"),[Const("N"),cmpPara])
    eq2=isabelle.eq(left2,makeite("isPara"))
    dontCareVarExp=Const("dontCareVar")
    left3=Fun(Const("env"),[Const("N"),dontCareVarExp])
    eq3=isabelle.eq(left3,Const("anyType"))
    primrec = isabelle.primRec(
        "env",
        FunType(isabelle.nat,isabelle.ConstType("envType")),
        [eq1,eq2,eq3])
    res=[]
    
    proof=isabelle.AutoProof()
    lemmas=IsabelleLemmas(name="env_simp",lemmas=paraLemmas,proof=[proof])
    
    res.append(primrec)
    res.append(lemmas)
    return res

def check_ite_assign_cmd(c):
    """If c is of the form if b then v := e1 else v := e2 end,
    return (b, v, e1, e2). Otherwise, return None.
    
    """
    if isinstance(c, murphi.IfCmd):
        if len(c.if_branches) == 1 and c.else_branch is not None:
            cond, if_cmds = c.if_branches[0]
            if len(if_cmds) == 1 and len(c.else_branch) == 1:
                c1, c2 = if_cmds[0], c.else_branch[0]
                if isinstance(c1, murphi.AssignCmd) and isinstance(c2, murphi.AssignCmd) and \
                    c1.var == c2.var:
                    return (cond, c1.var, c1.expr, c2.expr)

def translateCmd(cmd: murphi.MurphiCmd, vars: List[str]):
    if isinstance(cmd, murphi.Skip):
        return Const("skip")
    elif isinstance(cmd, murphi.AssignCmd):
        return isabelle.assignS(translateVar(cmd.var, vars), translateExp(cmd.expr, vars))
    elif isinstance(cmd, murphi.UndefineCmd):
        return None
    elif isinstance(cmd, murphi.ForallCmd):
        excl_form = abstract.check_forall_exclude_cmd(cmd)
        if excl_form:
            excl_var, concl = excl_form
            assert excl_var in vars
            vars.append(cmd.var)
            res = isabelle.forallExclS(cmd.var, translateCmds(concl, vars), excl_var, "N")
            del vars[-1]
            return res
        else:
            vars.append(cmd.var)
            res = isabelle.forallS(cmd.var, translateCmds(cmd.cmds, vars), "N")
            del vars[-1]
            return res
    elif isinstance(cmd, murphi.IfCmd):
        ite_assign_form = check_ite_assign_cmd(cmd)
        if ite_assign_form:
            cond, var, s1, s2 = ite_assign_form
            res = isabelle.assignS(translateVar(var, vars), isabelle.iteF(translateForm(cond, vars), translateExp(s1, vars), translateExp(s2, vars)))
            return res
        else:
            cond, c1 = cmd.if_branches[0]
            if len(cmd.if_branches) == 1:
                if cmd.else_branch:
                    isa_c2 = translateCmds(cmd.else_branch, vars)
                else:
                    isa_c2 = translateCmd(murphi.Skip(), vars)
            else:
                isa_c2 = translateCmd(murphi.IfCmd(cmd.args[2:]), vars)
            return isabelle.ITE("iteStm", translateForm(cond, vars), translateCmds(c1, vars), isa_c2)
    else:
        print("translateCmd: %s" % cmd)
        raise NotImplementedError
    
def translateCmds(cmds: Iterable[murphi.MurphiCmd], vars: List[str]):
    isa_cmds = []
    for cmd in cmds:
        isa_cmd = translateCmd(cmd, vars)
        if isa_cmd is not None:
            isa_cmds.append(isa_cmd)
    return isabelle.parallelS(isa_cmds)

def translateRuleTerm(rule: murphi.MurphiRule, vars: List[str]):
    isa_cond = translateForm(rule.cond, vars)
    isa_cmds = translateCmds(rule.cmds, vars)
    return Op("|>", isa_cond, isa_cmds)

def translateRule(rule: murphi.MurphiRule):
    isa_rule = translateRuleTerm(rule, [])
    typ = isabelle.rule
    args = []
    if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds):
        typ = FunType(isabelle.nat, typ)
        args.append("N")
    return Definition(rule.name, typ, isa_rule, args=args, is_equiv=True)

def translateRuleSet(ruleset: murphi.MurphiRuleSet):
    typ = isabelle.rule
    vars = []
    if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds):
        typ = FunType(isabelle.nat, typ)
        vars.append("N")
    for var_decl in ruleset.var_decls:
        typ = FunType(isabelle.nat, typ)
        vars.append(var_decl.name)
    isa_rule = translateRuleTerm(ruleset.rule, vars)
    return Definition(ruleset.rule.name, typ, isa_rule, args=vars, is_equiv=True)



#generate def of rs, and  lemma items on deriveRule, symProts, and terms rs N  in rules--such as Trys
#deriveAll lemmas such as r ∈ Trys N ⟹ deriveRule (env N) r
'''definition Trys :: "nat \\<Rightarrow> rule set" where
  "Trys N \\<equiv> oneParamCons N Try"
  definition NI_Remote_Get_Put_refs :: "nat \\<Rightarrow> rule set" where [rules_simp]:
  "NI_Remote_Get_Put_refs N \\<equiv> twoParamsCons N (NI_Remote_Get_Put_ref N)
 
lemma deriveAll:
  "r \\<in> Trys N \\<Longrightarrow> deriveRule (env N) r"
  "r \\<in> Crits N \\<Longrightarrow> deriveRule (env N) r"
  "r \\<in> Exits N \\<Longrightarrow> deriveRule (env N) r"
  "r \\<in> Idles N \\<Longrightarrow> deriveRule (env N) r"
  by (auto simp: deriveRule_def deriveForm_def deriveStmt_def
      Trys_def Try_def Crits_def Crit_def Exits_def Exit_def Idles_def Idle_def)

lemma symProtAll:
  "symProtRules' N (Trys N)"
  "symProtRules' N (Crits N)"
  "symProtRules' N (Exits N)"
  "symProtRules' N (Idles N)"
  using symTry(1) Trys_def symCrit(1) Crits_def symExit(1) Exits_def
    symIdle(1) Idles_def
    symParaRuleInfSymRuleSet by auto 

definition rules :: "nat \\<Rightarrow> rule set" where
  "rules N \\<equiv> Trys N \\<union> Crits N \\<union> Exits N \\<union> Idles N"

  "'''

def translateRuleSets(ruleset: murphi.MurphiRuleSet):
    typ = isabelle.rule
    vars = []
    if "N" in (decl.name for decl in ruleset.var_decls):
        pass
    else:
        if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds):
            vars.append("N")
    for var_decl in ruleset.var_decls:
        vars.append(var_decl.name)
    if "N" in vars:
        count = len(vars) - 1
    else:
        count = len(vars)

    typ = FunType(isabelle.nat, isabelle.setType(isabelle.rule))
    NParam = Const("N")
    ruleParam = Fun(Const(ruleset.rule.name),[NParam]) if ("N" in vars) else Const(ruleset.rule.name)
    if count == 1:
        isa_rule = Fun(Const("oneParamCons"),[Const("N"),ruleParam])
    else:
        isa_rule = Fun(Const("twoParamsCons"),[Const("N"),ruleParam])
    def1=Definition(ruleset.rule.name+"s", typ, isa_rule, args=["N"], is_equiv=True)
    assm1=Op(":",Const("r"),Fun(Const(ruleset.rule.name+"s"),[Const("N")]))
    cons1=Fun(Const("deriveRule"), \
    [Fun(Const("env"),[Const("N")]),Const("r")])
    lemma1=IsabelleLemma(assms=[assm1],conclusion=cons1,inLemmas=True)
    unfolds1=[ruleset.rule.name+"s",ruleset.rule.name]
    usings2=["sym"+ruleset.rule.name+"(1)",ruleset.rule.name+"s_def"]

    cons2=Fun(Const("symProtRules'"),[Const("N"), \
        Fun(Const(ruleset.rule.name+"s"),[Const("N")])])
    
    lemma2=IsabelleLemma(assms=[],conclusion=cons2,inLemmas=True)
    term=Fun(Const(ruleset.rule.name+"s"),[Const("N")])

    return (def1,lemma1,lemma2,term,unfolds1,usings2)

def translateRule1(rule: murphi.MurphiRule):
    vars = []
    if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds):
        vars.append("N")

    typ = FunType(isabelle.nat, isabelle.setType(isabelle.rule)) if "N" in vars else isabelle.setType(isabelle.rule)
    ruleParam = Fun(Const(rule.name), [Const("N")]) if ("N" in vars) else Const(rule.name)
    def1 = Definition(rule.name+"s", typ, isabelle.Set(ruleParam), args=vars, is_equiv=True)
    opds = [Const(n) for n in vars]
    assm1 = Op(":",Const("r"),Fun(Const(rule.name+"s"),opds))
    cons1 = Fun(Const("deriveRule"), [
        Fun(Const("env"), [Const("N")]),
        Const("r")])
    lemma1 = IsabelleLemma(assms=[assm1],conclusion=cons1,inLemmas=True)
    unfolds1 = [rule.name+"s",rule.name]
    usings2 = ["sym"+rule.name+"(1)", rule.name+"s_def"]

    cons2 = Fun(Const("symProtRules'"), [
        Const("N"),
        Fun(Const(rule.name+"s"),opds)])
    
    lemma2 = IsabelleLemma(assms=[],conclusion=cons2,inLemmas=True)
    term = Fun(Const(rule.name+"s"),opds)
    return def1, lemma1, lemma2, term, unfolds1, usings2


def translateInvariant(inv: murphi.MurphiInvariant):
    typ = isabelle.formula
    args = []
    if hasParamExpr(inv.inv):
        typ = FunType(isabelle.nat, typ)
        args.append("N")
    # Extract two parameters
    inv_t = inv.inv
    for _ in range(2):
        assert isinstance(inv_t, murphi.ForallExpr)
        typ = FunType(isabelle.nat, typ)
        args.append(inv_t.var)
        inv_t = inv_t.expr
    isa_inv = translateForm(inv_t, args)
    return Definition(inv.name, typ, isa_inv, args=args, is_equiv=True)

def genRuleSetSymLemma(ruleset: murphi.MurphiRuleSet):
    """Generate symmetry and wellformedness for each rule.
    
    lemma symTry:
        "symParamRule N Try"
        "[|i <= N|] ==> wellFormedRule (env N) N (Try i)"
        unfolding Try_def
        apply (auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall
                            symParamFormForallExcl symParamFormImply symParamStatementParallel
                            symParamStatementForall symParamStatementForallExcl symParamStatementIte)
        unfolding symParamForm_def symParamStatement_def symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def
        apply auto
        done
    """
    vars = []
    hasForall=False
    if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds):
        vars.append("N")
        hasForall=True
    for var_decl in ruleset.var_decls:
        vars.append(var_decl.name)
    paraNums=len(vars) - 1 if hasForall else len(vars)
    args=list(map(lambda a: Const(a),vars))
    ruleConst=Fun(Const(ruleset.rule.name),[Const("N")]) if hasForall else Const(ruleset.rule.name)
    ruleInst=Fun(Const(ruleset.rule.name),args) #if args==[] else Fun(Const("wellFormedRule"),[Const("N") ]) #Const(def_name) if args==[] else  
    predic1=Fun(Const("symParamRule"),[Const("N"),ruleConst]) if paraNums==1 else Fun(Const("symParamRule2'"),[Const("N"),ruleConst])
    lemma1= IsabelleLemma(assms=[], conclusion=predic1,inLemmas=True)
    env=Fun(Const("env"),[Const("N")])
    predic2=Fun(Const("wellFormedRule"),[env,Const("N"),ruleInst])
    assms=[Op("<=",Const(n.name),Const("N")) for n in  ruleset.var_decls]
    lemma2= IsabelleLemma(assms=assms, conclusion=predic2,inLemmas=True)
    intros=["symParamRuleI2", "symParamRuleI", "symParamFormAnd", "symParamFormForall",
            "symParamFormForallExcl", "symParamFormImply" ,"symParamStatementParallel",
            "symParamStatementForall", "symParamStatementForallExcl", "symParamStatementIte"] if paraNums==1 else \
           ["symParamRuleI2", "symParamRuleI", "symParamForm2And", "symParamForm2Forall1",
            "symParamForm2Forall2", "symParamFormForallExcl2", "symParamForm2Imply", "symParamStatementParallel",
            "symParamStatementForall", "symParamStatementForallExcl", "symParamStatementIte"]
 
    proof1=isabelle.AutoProof(unfolds=[ruleset.rule.name], introITag="intro!", intros=intros)
    proof2=isabelle.AutoProof(unfolds=["symParamForm", "symParamStatement",
                                       "symParamForm2", "symParamStatement2", "mutualDiffVars", "equivForm"])
    lemmas= IsabelleLemmas(name="sym"+ruleset.rule.name,lemmas=[lemma1,lemma2],proof=[proof1,proof2])
    return lemmas

def makeSymProtAllProof(usings):
    i=0
    proofs=[]
    while i< len(usings):
        thisUsings=[usings[i],usings[i+1],"symParaRuleInfSymRuleSet", "symParaRuleInfSymRuleSet2"]
        proofs.append(isabelle.AutoProof(usings=thisUsings,goalNum="1"))
        i=i+2
    return proofs

def translateAllSpecs(prot: murphi.MurphiProtocol):
    res = []
    rulesDefList = []
    deriveAllLLemmaist = []
    symProtAllLemmaList = []
    deriveAllLLemmaProofUnfolds1 = []
    symProtAllLemmaProofUsings2 = []
    
    for decl in prot.decls:
        if isinstance(decl, murphi.MurphiRule):
            res.append(translateRule(decl))
            if decl not in prot.abs_rule_map.values():
                res.append(genRuleSymLemma(decl))
            def1,lemma1,lemma2,term1,unfolds,usings=translateRule1(decl)
            res.append(def1)
            deriveAllLLemmaist.append(lemma1)
            if decl in prot.ori_rule_map.values():
                symProtAllLemmaList.append(lemma2)
                rulesDefList.append(term1)
            deriveAllLLemmaProofUnfolds1.extend(unfolds)
            if decl in prot.ori_rule_map.values():
                symProtAllLemmaProofUsings2.extend(usings)

        elif isinstance(decl, murphi.MurphiRuleSet):
            res.append(translateRuleSet(decl))
            if decl not in prot.abs_rule_map.values():
                res.append(genRuleSetSymLemma(decl))
            def1,lemma1,lemma2,term1,unfolds,usings=translateRuleSets(decl)
            res.append(def1)
            deriveAllLLemmaist.append(lemma1)
            if decl in prot.ori_rule_map.values():    
                symProtAllLemmaList.append(lemma2)
                rulesDefList.append(term1)
            deriveAllLLemmaProofUnfolds1.extend(unfolds)
            if decl in prot.ori_rule_map.values():
                symProtAllLemmaProofUsings2.extend(usings)

        elif isinstance(decl, murphi.MurphiInvariant):
            res.append(translateInvariant(decl))

    typ = FunType(isabelle.nat, isabelle.setType(isabelle.rule))
    def_rules = Definition(name="rules", typ=typ, val=isabelle.UN(rulesDefList), args=["N"])
    res.append(def_rules)
    deriveAllLLemmaProof = [isabelle.AutoProof(
        unfolds=["deriveRule", "deriveForm", "deriveStmt"] + deriveAllLLemmaProofUnfolds1)]
    symProtAllLemmaProof = makeSymProtAllProof(symProtAllLemmaProofUsings2)
    deriveAllLLemmas = IsabelleLemmas("deriveAll", deriveAllLLemmaist, proof=deriveAllLLemmaProof)
    symProtAllLemmas = IsabelleLemmas("symProtAll", symProtAllLemmaList, proof=symProtAllLemmaProof)
    res.append(deriveAllLLemmas)
    res.append(symProtAllLemmas)
    return res

def genRuleSymLemma(rule: murphi.MurphiRule):
    args = []
    if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds):
        args.append("N")
    oldArgs=args.copy()
    args=list(map(lambda a: Const(a),args))
    ruleInst=Fun(Const(rule.name),args)
    predic1=Fun(Const("symProtRules'"),[Const("N"),isabelle.Set(ruleInst)])  
    lemma1= IsabelleLemma(assms=[], conclusion=predic1,inLemmas=True)  
    env=Fun(Const("env"),[Const("N")])
    predic2=Fun(Const("wellFormedRule"),[env,Const("N"),ruleInst])
    intros=["equivStatementParallel","equivStatementIteStm","equivStatementPermute"]
    proof=[isabelle.AutoProof(unfolds=[rule.name])] if "N" not in oldArgs else \
        [isabelle.AutoProof(unfolds=[rule.name],introITag="intro!",intros=intros), \
        isabelle.IsabelleApplyRuleProof(name="equivStatementSym"), isabelle.IsabelleApplyRuleProof(name="equivStatementPermute"), \
        isabelle.AutoProof(simpadds=["mutualDiffVars_def"])]
    lemma2= IsabelleLemma(assms=[], conclusion=predic2,inLemmas=True)
    lemmas= IsabelleLemmas(name="sym"+rule.name,lemmas=[lemma1,lemma2],proof=proof)
    return lemmas
  
def genInvariantSymLemma(inv: murphi.MurphiInvariant) -> IsabelleLemma:
    """Generate symmetry for property of invariant.

    lemma sym<inv_name>:
        "symParamForm2 N (<inv_name> N)"
        unfolding <inv_name>_def
        apply auto
        apply (intro symParamForm2Imply symParamFormForallExcl2)
        unfolding symParamForm2_def
        apply auto
        done
    """
    invN = Fun(Const(inv.name), [Const("N")])
    return IsabelleLemma(
        name="sym" + inv.name,
        assms=[],
        conclusion=Fun(Const("symParamForm2"), [Const("N"), invN]),
        proof=[
            isabelle.AutoProof(unfolds=[inv.name]),
            isabelle.introProof(rules=["symParamForm2Imply", "symParamFormForallExcl2"]),
            isabelle.AutoProof(unfolds=["symParamForm2"])
        ]
    )

'''
lemma symInvs:
  "symParamForm2 N (Lemma_1 N)"
  "symParamForm2 N (Lemma_2a N)"
  "symParamForm2 N (Lemma_2b N)"
  "symParamForm2 N (Lemma_3a N)"
  "symParamForm2 N (Lemma_3b N)"
  "symParamForm2 N (Lemma_4 N)"
  unfolding Lemma_1_def Lemma_2a_def Lemma_2b_def Lemma_3a_def Lemma_3b_def Lemma_4_def apply auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  done'''    

def genSymLemmas(prot: murphi.MurphiProtocol):
    res = []
    for decl in prot.decls:
        if isinstance(decl, murphi.MurphiInvariant):
            res.append(genInvariantSymLemma(decl))
    return res  

class extMurphiInvariant:
    def __init__(self, decl):
        assert(isinstance(decl,murphi.MurphiInvariant))
        self.decl = decl

    def __str__(self):
        return str(self.decl)

    def __repr__(self):
        return "murphiInvariant(%s)" % (', '.join(repr(typ) for typ in self.typs))

    def __eq__(self, other):
        return isinstance(other,extMurphiInvariant) and self.decl == other.decl

    def genLemma1(self):
        typ = isabelle.formula
        args = []
        if hasParamExpr(self.decl.inv):
            typ = FunType(isabelle.nat, typ)
            args.append("N")
        # Extract two parameters
        inv_t = self.decl.inv
        for _ in range(2):
            assert isinstance(inv_t, murphi.ForallExpr)
            typ = FunType(isabelle.nat, typ)
            args.append(inv_t.var)
            inv_t = inv_t.expr
        #inv_t  = e1 ->e2 for some e1,e2 e2=forall i~=j-->  
        # 
        assert(isinstance(inv_t , murphi.OpExpr)&(inv_t.op=="->"))
        excl_form = abstract.check_forall_exclude_form(inv_t.expr2)
        if excl_form:
            var2=inv_t.expr2.var_decl.name
            assert ((var2 not in args))
            args.append(var2)
            del(args[1])
            expr2=inv_t.expr2.expr
            exprNeg=expr2.expr1 #exprNeg is "(i=j)"
            tmpLeft=exprNeg.expr1
            exprNeg.expr1=exprNeg.expr2
            exprNeg.expr2=tmpLeft
            self.lemma1Eqlemma =False
            res = translateForm(murphi.OpExpr("->",murphi.OpExpr("&",expr2.expr1,inv_t.expr1),expr2.expr2),args)
        else:
            #vars.append(e.var)
            res = translateForm(self.decl.inv.expr.expr, args)
            self.lemma1Eqlemma =True
        return Definition(self.decl.name+"'", typ, res, args=args, is_equiv=True)

    '''lemma absTransfLemma1:
    "M < N ⟹ M = 1 ⟹ l ≤ 1 ⟹ absTransfForm (env N) M (Lemma_1' N 0 l) = Lemma_1' N 0 l"
    unfolding Lemma_1'_def by auto'''
    def genabsTransfLemma(self):
        cond1=Op("<",Const("M"),Const("N"))
        cond2=Op("=",Const("M"),Const("1"))
        cond3=Op("<=",Const("l"),Const("1"))
        right=Fun(Const(self.decl.name+"'"),[Const("N"),Const("0"),Const("l")])
        left=Fun(Const("absTransfForm"),[Fun(Const("env"),[Const("N")]),Const("M"),
            right])
        proof=isabelle.AutoProof(unfolds=[self.decl.name+"'"])
        return(IsabelleLemma(name="absTransf"+self.decl.name+"'",assms=[cond1,cond2,cond3],conclusion=Op("=",left,right),proof=[proof]))
    '''"lemma absTransfLemma1M < N ⟹ M = 1 ⟹ l ≤ 1 ⟹ 
    safeForm  env  M (pf 0 i) ∧ deriveForm env (pf 0 i)
    unfolding Lemma_1'_def by auto"'''

    def genSafeAndderiveForm(self):
        """
        """
        cond1=Op("<",Const("M"),Const("N"))
        cond2=Op("=",Const("M"),Const("1"))
        cond3=Op("<=",Const("l"),Const("M"))
        cond4=Op("<=",Const("k"),Const("M"))
        pred1=Fun(Const("safeForm"), \
            [Fun(Const("env"),[Const("N")]), Const("M"), \
            Fun(Const(self.decl.name+"'"),[Const("N"),Const("k"),Const("l")])])
        pred2=Fun(Const("deriveForm"), \
            [Fun(Const("env"),[Const("N")]),   \
            Fun(Const(self.decl.name+"'"),[Const("N"),Const("k"),Const("l")])])
        return IsabelleLemma(
            name="SafeAndderiveForm"+self.decl.name+"'",
            assms=[cond1,cond2,cond3,cond4], \
            conclusion=Op("&",pred1,pred2),
            proof=[isabelle.AutoProof(unfolds=[self.decl.name+"'"])])
  
    def genstrengthenVsObsLemma(self):
        """For each invariant, generate strengthenVsObs lemma.
        
        lemma strengthenVsObsLemma_1:
            "strengthenVsObs (Lemma_1 N) (Lemma_1' N) N"
            unfolding Lemma_1_def Lemma_1'_def
            apply (rule strengthenVsObsDiff)
            unfolding symParamForm_def apply auto

        lemma strengthenVsObsLemma_2a :
            "strengthenVsObs (Lemma_2a N) (Lemma_2a' N) N"
            unfolding Lemma_2a_def Lemma_2a'_def
            apply (rule strengthenVsObsSame)
        """
        opd1 = Fun(Const(self.decl.name),[Const("N")])
        opd2 = Fun(Const(self.decl.name+"'"),[Const("N")])
        pred = Fun(Const("strengthenVsObs"), [opd1, opd2, Const("N")])
        proofs = []
        if self.lemma1Eqlemma:
            proofs.append(isabelle.IsabelleApplyRuleProof(
                name="strengthenVsObsSame",
                unfolds=[self.decl.name,self.decl.name+"'"]))
        else:
            proofs.append(isabelle.IsabelleApplyRuleProof(
                name="strengthenVsObsDiff",
                unfolds=[self.decl.name,self.decl.name+"'"]))
            proofs.append(isabelle.AutoProof(unfolds=["symParamForm"]))
        lemma = IsabelleLemma(
            name="strengthenVsObs" + self.decl.name,
            assms=[], conclusion=pred, proof=proofs)
        return lemma

    def genSymInvsItem1(self):
        """For each invariant, generate symParamForm lemma.

        lemma "symParamForm2 N (<name> N)"
            subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
                unfolding symParamForm2_def by auto
            done
        """
        name = self.decl.name + "'"
        pred = Fun(Const("symParamForm2"), [
            Const("N"),
            Fun(Const(name), [Const("N")])])
        lemma = IsabelleLemma(assms=[],conclusion=pred,inLemmas=True)
        proof = isabelle.subgoalProof(proofs=[
            isabelle.introProof(rules=["symParamForm2Imply", "symParamFormForallExcl2"]),
            isabelle.AutoProof(unfolds=["symParamForm2"])])
        return name, lemma, proof


class extMurphiRule:
    def __init__(self, decl):
        assert(isinstance(decl,murphi.MurphiRule))
        self.decl = decl

    def __str__(self):
        return str(self.decl)

    def __repr__(self):
        return "murphiRule(%s)" % (', '.join(repr(typ) for typ in self.typs))

    def __eq__(self, other):
        return isinstance(other, extMurphiRule) and self.decl == other.decl

    '''lemma strengthenVsObsLs_lemmasFor_NI_InvAck1:
    "strengthenVsObsLs (lemmasFor_NI_InvAck1 N) (lemmasFor_NI_InvAck1' N) N"
     by (auto simp add: strengthenVsObsLs_def lemmasFor_NI_InvAck1_def lemmasFor_NI_InvAck1'_def)'''

    def genLemmastrengthenVsObsLs(self):
        name="strengthenVsObsLs_lemmasFor_"+self.decl.name
        opd1=Fun(Const("lemmasFor_"+self.decl.name),[Const("N")])
        opd2=Fun(Const("lemmasFor_"+self.decl.name+"'"),[Const("N")])
        pred=Fun(Const("strengthenVsObsLs"),[opd1,opd2,Const("N")])
        unfolds=["strengthenVsObsLs", "lemmasFor_"+self.decl.name, "lemmasFor_"+self.decl.name+"'"]
        proof=isabelle.AutoProof(unfolds=unfolds)
        lemma=IsabelleLemma(name=name,assms=[],conclusion=pred,proof=[proof])
        return lemma

    def genStrengthenLemmasDef1(self, item):
        return Definition(
            name="lemmasFor_" + self.decl.name + "'",
            typ=FunType(isabelle.nat, isabelle.ListType(FunType(isabelle.nat,FunType(isabelle.nat,isabelle.formula)))),
            val=isabelle.List(*tuple(Fun(Const(lemma+"'"), [Const("N")]) for lemma in item["strengthen"])),
            args=["N"]
        )

    def genFitenvLemma(self):
        if hasParamExpr(self.decl.cond) or any(hasParamCmd(c) for c in self.decl.cmds):
            hasNList = [Const("N")]
        else:
            hasNList = []
         
        return IsabelleLemma(
            name="lemma" + self.decl.name + "_fitEnv",
            assms=[
                Fun(Const("formEval"), [Fun(Const("pre"),[Const("r")]),Const("s")]),
                Fun(Const("fitEnv"), [Const("s"),Fun(Const("env"),[Const("N")])]),
                Op(":",Const("r"), Fun(Const(self.decl.name+"_refs"),hasNList))
            ],
            conclusion=Fun(Const("fitEnv"),
                [Fun(Const("trans1"),[Fun(Const("act"),[Const("r")]),Const("s")]), \
                 Fun(Const("env"),[Const("N")])
            ]),
            attribs=["intro"],
            proof=[isabelle.AutoProof(unfolds=[self.decl.name+"_refs", self.decl.name+"_ref"])]
        )


'''generate items on strengthening and abstraction, firstly generate strengthened rule and abstract resultings

lemma Idle_strengthen:
  "strengthenRuleByFrmL2 (map2' (lemmasFor_Idle N) j i) (Idle i) = Idle_ref N i"
  unfolding lemmasFor_Idle_def Lemma_1_def Idle_def Idle_ref_def by auto


lemma IdleStrengthRel:"strengthenRel (Idles N)  (set (InvS N)) (Idle_refs N) N "
  apply(unfold Idles_def Idle_refs_def)
  apply(rule_tac ?lemmasFor_r="lemmasFor_Idle" in strengthenExt1)
  using Idle_strengthen apply presburger
  apply(unfold InvS_def,auto)    
  done


definition lemmasFor_Idle :: "nat \\<Rightarrow> (nat \\<Rightarrow> nat \\<Rightarrow> formula) list" where
  "lemmasFor_Idle N \\<equiv> [Lemma_1 N]"

definition lemmasFor_Idle' :: "nat \\<Rightarrow> (nat \\<Rightarrow> nat \\<Rightarrow> formula) list" where
  "lemmasFor_Idle' N \\<equiv> [Lemma_1' N]"

definition InvS :: "nat \\<Rightarrow> (nat \\<Rightarrow> nat \\<Rightarrow> formula) list list" where
  "InvS N \\<equiv> [lemmasFor_Idle N]"
'''


class extMurphiRuleSet:
    def __init__(self, decl, strengthen=None):
        assert(isinstance(decl,murphi.MurphiRuleSet))
        self.decl = decl
        self.strengthen=strengthen

    def __str__(self):
        return str(self.decl)

    def __repr__(self):
        return "murphiRuleset(%s)" % (', '.join(repr(typ) for typ in self.typs))

    def __eq__(self, other):
        return isinstance(other, extMurphiRuleSet) and self.decl == other.decl

    '''lemma strengthenVsObsLs_lemmasFor_NI_InvAck1:
    "strengthenVsObsLs (lemmasFor_NI_InvAck1 N) (lemmasFor_NI_InvAck1' N) N"
     by (auto simp add: strengthenVsObsLs_def lemmasFor_NI_InvAck1_def lemmasFor_NI_InvAck1'_def)'''

    def genLemmastrengthenVsObsLs(self):
        name="strengthenVsObsLs_lemmasFor_"+self.decl.rule.name
        opd1=Fun(Const("lemmasFor_"+self.decl.rule.name),[Const("N")])
        opd2=Fun(Const("lemmasFor_"+self.decl.rule.name+"'"),[Const("N")])
        pred=Fun(Const("strengthenVsObsLs"),[opd1,opd2,Const("N")])
        unfolds=["strengthenVsObsLs", "lemmasFor_"+self.decl.rule.name, "lemmasFor_"+self.decl.rule.name+"'"]
        autoIntros=["strengthenVsObs"+k for k in self.strengthen]
        if self.strengthen==[]:
            proof=isabelle.AutoProof(unfolds=unfolds)
        else:
            proof=isabelle.AutoProof(unfolds=unfolds,introITag="intro",intros=autoIntros)
        lemma=IsabelleLemma(name=name,assms=[],conclusion=pred,proof=[proof])
        return(lemma)

    def genStrengthenLemmasDef1(self,item):
        name="lemmasFor_"+self.decl.rule.name+"'"
        val=isabelle.List(*tuple(Fun(Const(lemma+"'"), [Const("N")]) for lemma in item["strengthen"]))
        typ = FunType(isabelle.nat, isabelle.ListType(FunType(isabelle.nat,FunType(isabelle.nat,isabelle.formula))))
        defLemma=Definition(name=name, typ=typ, val=val,args=["N"])
        return(defLemma)

    def genFitenvLemma(self):
        name="lemma"+self.decl.rule.name+"_fitEnv"
        hasNList=[Const("N")] if len(self.decl.var_decls)!=0  else \
            ([Const("N")] if (hasParamExpr(self.decl.rule.cond) or any(hasParamCmd(c) for c in self.decl.rule.cmds)) else [])
        assm1=Fun(Const("formEval"), [Fun(Const("pre"),[Const("r")]),Const("s") ])  
        assm2=Fun(Const("fitEnv"), [Const("s"),Fun(Const("env"),[Const("N")]) ])  
        assm3=Op(":",Const("r"),Fun(Const(self.decl.rule.name+"_refs"),hasNList) )
        conclusion=Fun(Const("fitEnv"), \
        [Fun(Const("trans1"),[Fun(Const("act"),[Const("r")]),Const("s")]), \
        Fun(Const("env"),[Const("N")]) \
        ]) 
        #atrributs=["intro"]
        unfolds=[ self.decl.rule.name+"_refs", self.decl.rule.name+"_ref"]
        proof=isabelle.AutoProof(unfolds=unfolds)
        #attribs=atrributs, 
        return(IsabelleLemma(name=name,assms=[assm1,assm2,assm3],conclusion=conclusion,proof=[proof]))

def genStrengthenLemmas(prot: murphi.MurphiProtocol, strengthenSpec):
    def getRuleOrRuleset(item):
        if "ruleset" in item:
            return item["ruleset"]
        else:
            return item["rule"]

    def getAllProtRuleNames():
        return [k for k, r in prot.ori_rule_map.items() if isinstance(r, murphi.MurphiRule)]

    def getAllProtRuleSetNames():
        return [k for k, r in prot.ori_rule_map.items() if isinstance(r, murphi.MurphiRuleSet)]

    res = []
    InvSList = []
    InvS1List = []
    res1 = []
    deriveAllLLemmaist = []
    symProtAllLemmaList = []
    refRulesDefList = []
    defOfabsRules = []
    absRuleDefList = []
    absRuleDefList1 = []

    deriveAllLLemmaProofUnfolds1 = []
    symProtAllLemmaProofUsings2 = []
    
    absLemmasOnSets=[]

    for item in strengthenSpec:
        if "ruleset" in item:
            ruleset: murphi.MurphiRuleSet = prot.ori_rule_map[item["ruleset"]]
            vars = []
            hasForall=False
            if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds):
                vars.append("N")
                hasForall=True
            for var_decl in ruleset.var_decls:
                vars.append(var_decl.name)
            paraNums=len(vars) - 1 if hasForall else len(vars)

            # Generate definition for strengthening lemmas for this rule
            typ = FunType(isabelle.nat, isabelle.ListType(FunType(isabelle.nat,FunType(isabelle.nat,isabelle.formula))))
            val=isabelle.List(*tuple(Fun(Const(lemma), [Const("N")]) for lemma in item["strengthen"]))
            defLemma=Definition(name="lemmasFor_"+ruleset.rule.name, \
            typ=typ, val=val,args=["N"])

            # Generate r_ref
            r_ref=murphi.MurphiRule(name=ruleset.rule.name+"_ref",cond=ruleset.rule.cond,cmds=ruleset.rule.cmds)
            strengthenCopy=item["strengthen"].copy()
            strengthenCopy.reverse()
            for lemma in strengthenCopy:
                lemmaC = prot.lemma_map[lemma].inv
                r_ref = abstract.strengthen(r_ref,lemmaC)
            oldRuleName=ruleset.rule.name
            #r_ref.name=ruleset.rule.name+"_ref"
            ruleSet1=murphi.MurphiRuleSet(var_decls=ruleset.var_decls,rule=r_ref)
            #generate lemmas on r_strengthen
            oldhasNList=[Const("N")] if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds) else []
        
            hasNList=[Const("N")] if hasParamExpr(ruleSet1.rule.cond) or any(hasParamCmd(c) for c in ruleSet1.rule.cmds) else []
            
            left1=Fun(Const("strengthenRuleByFrmL2"), [\
                Fun(Const("map2'"),[Fun(Const("lemmasFor_"+oldRuleName),[Const("N")]),Const("j"),Const("i")]), \
                Fun(Const(oldRuleName), oldhasNList+[Const("i")]) \
                ]) if (paraNums==1) else \
                Fun(Const("strengthenRuleByFrmL2"), [\
                Fun(Const("map2'"),[Fun(Const("lemmasFor_"+oldRuleName),[Const("N")]),Const("i"),Const("j")]), \
                Fun(Const(oldRuleName), oldhasNList+[Const("i"),Const("j")]) \
                ])  
                
            right1=Fun(Const(r_ref.name),hasNList+[Const("i")]) if (paraNums==1) else \
                Fun(Const(r_ref.name),hasNList+[Const("i"),Const("j")])
            eq1=isabelle.eq(left1,right1)
            lemmas_def=" ".join(lemma+"_def" for lemma in item["strengthen"])
            proof=isabelle.AutoProof(unfolds=[("lemmasFor_%s_def %s %s_def %s_ref")%(oldRuleName,lemmas_def,oldRuleName,oldRuleName)])
            lemma1= IsabelleLemma(name=oldRuleName+"_strengthen",assms=[], conclusion=eq1,proof=[proof]) 
            #generate lemmas on r_StrengthRel
            pred2=Fun(Const("strengthenRel"), [ \
                Fun(Const(oldRuleName+"s"),[Const("N")]), \
                Fun(Const("set"), [Fun(Const("InvS"),[Const("N")])]), \
                Fun(Const(oldRuleName+"_refs"), [Const("N")]),
                Const("N") \
                ])
            proof21TacName="strengthenExt1" if len(ruleset.var_decls)==1 else "strengthenExt2"
            proof21=isabelle.IsabelleApplyRuleProof(name=proof21TacName,unfolds=["%ss_def %s_refs"%(oldRuleName,oldRuleName)],
            rule_tac="?lemmasFor_r=\"lemmasFor_"+oldRuleName+"\"")
            proof22=isabelle.presburgerProof(usings=[oldRuleName+"_strengthen"])
            proof23=isabelle.AutoProof(unfolds=["InvS"])
            lemma2=IsabelleLemma(name=oldRuleName+"StrengthRel",assms=[], conclusion=pred2,proof=[proof21,proof22,proof23]) 
            predOfLemma=Fun(Const(("lemmasFor_%s"%oldRuleName)),[Const("N")])
            predOfLemma1=Fun(Const(("lemmasFor_%s"%oldRuleName+"'")),[Const("N")])
            
            #abstract r_ref
            absRule=[]
            absRules=[]
            suffix=""
            if isinstance(ruleSet1,murphi.MurphiRuleSet):
                limits=dict()
                if len(ruleSet1.var_decls)==1:
                    limits[ruleSet1.var_decls[0].name]=False
                    absr=abstract.absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    if absr!=ruleSet1.rule and absr!=None:
                        prot.abs_rule_map[absr.name]=absr
                        prot.decls.append(absr)
                        absRule.append(absr)

                elif len(ruleSet1.var_decls)==2:
                    limits[ruleSet1.var_decls[0].name]=False
                    limits[ruleSet1.var_decls[1].name]=True
                    absr=abstract.absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    absrulesetdecls=ruleSet1.var_decls[1:2]
                    if absr!=ruleSet1.rule and absr!=None:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map[absr.name]=absruleset
                        prot.decls.append(absruleset)
                        absRules.append(absr)

                    limits=dict()
                    limits[ruleSet1.var_decls[1].name]=False
                    limits[ruleSet1.var_decls[0].name]=True
                    absr=abstract.absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    absrulesetdecls=ruleSet1.var_decls[0:1]
                    if absr!=ruleSet1.rule and absr!=None:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map[absr.name]=absruleset
                        prot.decls.append(absruleset)
                        absRules.append(absr)
                    limits=dict()
                    limits[ruleSet1.var_decls[0].name]=False
                    limits[ruleSet1.var_decls[1].name]=False
                    absr=abstract.absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    if absr!=ruleSet1.rule and absr!=None:
                        prot.abs_rule_map[absr.name]=absr
                        prot.decls.append(absr)
                        absRule.append(absr)
            def11,lemma11,lemma21,term11,unfolds1,usings1=translateRuleSets(ruleSet1)
            deriveAllLLemmaist.append(lemma11)
            symProtAllLemmaList.append(lemma21)
            refRulesDefList.append(term11)
            deriveAllLLemmaProofUnfolds1.extend(unfolds1)
            symProtAllLemmaProofUsings2.extend(usings1)

            InvSList.append(predOfLemma)
            InvS1List.append(predOfLemma1)
            res.append(defLemma)
            res.append(translateRuleSet(ruleSet1))
            res.append(genRuleSetSymLemma(ruleSet1))
            res.append(def11)
            res.append(lemma1)
            res1.append(lemma2)
            
            '''for absr in absRules:
                res.append(translateRuleSet(absr))
                defA,lemmaA1,lemmaA2,termA,unfoldsA,usingsA=translateRuleSets(absr)
                res.append(defA)'''
            '''generate1. lemmas on abstraction for r_refs by json:
            2. definitions for    ABS_rules,  ABS_rules' 
            "abstract":[{"cond":{"i": false},"answer":"ABS_Idle"},{"cond":{"i": true},"answer":"ABS_Idle"}]
            lemma abs_Idle_ref
            "M \\<le> N \\<Longrightarrow> i \\<le> M \\<Longrightarrow> absTransfRule (env N) M (Idle_ref N i) = Idle_ref M i"
            "M \\<le> N \\<Longrightarrow> i > M \\<Longrightarrow> absTransfRule (env N) M (Idle_ref N i) = ABS_Idle M
            definition ABS_rules :: "nat \\<Rightarrow> rule set" where [simp]:
            "ABS_rules M \\<equiv>
            Trys M \\<union> Crits M \\<union> {ABS_Crit} \\<union> Exits M \\<union> Idle_refs M \\<union> {ABS_Idle M} \\<union> {chaos \\<triangleright> skip}"

            definition ABS_rules' :: "nat \\<Rightarrow> rule set" where [simp]:
            "ABS_rules' M \\<equiv>
            ((Trys M) \\<union> {chaos \\<triangleright> skip}) \\<union>
            ((Crits M) \\<union> {ABS_Crit}) \\<union>
            ((Exits M) \\<union> {chaos \\<triangleright> skip}) \\<union>
            ((Idle_refs M) \\<union> {ABS_Idle M})"

            lemma ABS_rules_eq_rules':
            "ABS_rules M = ABS_rules' M"
            by auto"'''
            absLemmas=[]
            unfolds=[ruleSet1.rule.name]
            tmpabsRuleDefList1=[]  #for definition of rule ABS_rules
            tmpabsRuleDefListM1=[] #for lemma abs_Idle_refs
            for absItem in item["abstract"]:
                cond=absItem["cond"]
                assms=[Op("<=",Const("M"),Const("N")) ]
                abstracted=False
                absPars=[]
                leftPars=[]
                for k, val0 in cond.items():
                    leftPars.append(Const(k))
                    if val0:
                        isaCond0=Op("<=",Const(k),Const("M"))   
                        absPars.append(Const(k))  
                                    
                    else:
                        isaCond0=Op(">",Const(k),Const("M"))
                        abstracted=True
                    assms.append(isaCond0)
                arg1=Fun(Const("env"),[Const("N")])
                arg2=Const("M")
                hasNList=[Const("N")] if hasParamExpr(ruleSet1.rule.cond) or any(hasParamCmd(c) for c in ruleSet1.rule.cmds) else []
                arg3=Fun(Const(ruleSet1.rule.name),hasNList+leftPars) if item["ruleset"]!=item["answer"] else \
                    Fun(Const(item["ruleset"]),hasNList+leftPars)
                hasMList=[Const("M")] if hasParamExpr(ruleSet1.rule.cond) or any(hasParamCmd(c) for c in ruleSet1.rule.cmds) else []
                if abstracted and absItem["answer"]!="skipRule":
                    thisAbstractr=prot.abs_rule_map[absItem["answer"]]
                    thisAbstractr=thisAbstractr.rule if isinstance(thisAbstractr,murphi.MurphiRuleSet) else thisAbstractr
                    absRuleHasNList=[Const("N")] if hasParamExpr(thisAbstractr.cond) or any(hasParamCmd(c) for c in thisAbstractr.cmds) else [] 
                    absRuleHasMList=[Const("M")] if hasParamExpr(thisAbstractr.cond) or any(hasParamCmd(c) for c in thisAbstractr.cmds) else [] 
                    
                else:
                    absRuleHasNList=[]   
                    absRuleHasMList=[]
                
                right=Fun(Const(absItem["answer"]),absRuleHasMList+absPars) if (absItem["answer"]!="skipRule") and abstracted else \
                    Fun(Const(absItem["answer"]),hasMList+absPars) if (absItem["answer"]!="skipRule") else \
                    Const("skipRule")
                conclusion=isabelle.eq(Fun(Const("absTransfRule"),[arg1,arg2,arg3]),right)

                
                if absItem["answer"].startswith("ABS_"):
                    thisPara1= absRuleHasNList
                else:
                    thisPara1=[Const("N")]
                absRulesPredForAbsRules=Fun(Const(absItem["answer"]+"s"),thisPara1)  if (absItem["answer"]!="skipRule") else \
                    isabelle.Set(Const("skipRule"))
                if (absItem["answer"]!="skipRule") and abstracted:
                    pass
                if (absItem["answer"]!="skipRule"):
                    absRuleDefList.append(absRulesPredForAbsRules)
                tmpabsRuleDefList1.append(absRulesPredForAbsRules)
                if absItem["answer"].startswith("ABS_"):
                    thisPara= absRuleHasMList
                else:
                    thisPara=[Const("M")]
                absRulesPredForAbsRulesM=Fun(Const(absItem["answer"]+"s"),thisPara)  if (absItem["answer"]!="skipRule") else \
                    isabelle.Set(Const("skipRule"))
                tmpabsRuleDefListM1.append(absRulesPredForAbsRulesM)
                absLemmas.append(IsabelleLemma(assms=assms,conclusion=conclusion,inLemmas=True))
                unfolds.append(absItem["answer"])
            absRuleDefList1.append(isabelle.Tuple(isabelle.UN(tmpabsRuleDefList1)))
            simpadds = ["Let_def"]
            absLemma = IsabelleLemmas(name="abs_"+ruleSet1.rule.name,lemmas=absLemmas,proof=[isabelle.AutoProof(unfolds=unfolds,simpadds=simpadds)])
            res.append(absLemma)
            absAllLemmaOnItemAssm = Op("<",Const("M"),Const("N"))
            if len(ruleSet1.var_decls) == 2:
                tmpabsRuleDefListM1[1], tmpabsRuleDefListM1[2] = tmpabsRuleDefListM1[2], tmpabsRuleDefListM1[1]

            absAllLemmaOnItemPred=isabelle.eq(Op("`", \
            Fun(Const("absTransfRule"),[Fun(Const("env"),[Const("N")]), \
            Const("M")]),Fun(Const(ruleSet1.rule.name+"s"),[Const("N")])), \
                isabelle.Tuple(isabelle.UNLeft(tmpabsRuleDefListM1)))
            thisUnfolds=[None if isinstance(k,isabelle.Set) else k.fun.name for k in tmpabsRuleDefListM1]
            if None in thisUnfolds:
                thisUnfolds.remove(None)
            absLemmasOnSetItemProof=isabelle.IsabelleApplyRuleProof(name="absGen",unfolds=thisUnfolds) if len(ruleSet1.var_decls)==1 else isabelle.IsabelleApplyRuleProof(name="absGen2",unfolds=thisUnfolds)
            absLemmasOnSetItem=IsabelleLemma(name="Abs_"+ruleSet1.rule.name+"s", assms=[absAllLemmaOnItemAssm], conclusion=absAllLemmaOnItemPred, \
                proof=[absLemmasOnSetItemProof,isabelle.AutoProof(usings=["abs_"+ruleSet1.rule.name])]) 
            absLemmasOnSets.append(absLemmasOnSetItem)
        else:
            rule: murphi.MurphiRule = prot.ori_rule_map[item["rule"]]
            vars = []
            hasForall = False
            if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds):
                vars.append("N")
                hasForall = True
            '''for var_decl in rule.var_decls:
                vars.append(var_decl.name)'''
            paraNums = len(vars) - 1 if hasForall else len(vars)

            # Generate definition for strengthening lemmas for this rule
            typ = FunType(isabelle.nat, isabelle.ListType(FunType(isabelle.nat,FunType(isabelle.nat,isabelle.formula))))
            val=isabelle.List(*tuple(Fun(Const(lemma+"'"), [Const("N")]) for lemma in item["strengthen"]))
            defLemma=Definition(name="lemmasFor_"+rule.name, \
            typ=typ, val=val,args=["N"])

            # Generate r_ref
            r_ref = murphi.MurphiRule(name=rule.name+"_ref",cond=rule.cond,cmds=rule.cmds)
            '''for lemma in item["strengthen"]:
                lemmaC=prot.lemma_map[lemma].inv
                r_ref=abstract.strengthen(r_ref,lemmaC)'''
            oldRuleName = rule.name

            # Generate lemmas on r_strengthen
            oldhasNList = [Const("N")] if hasParamExpr(r_ref.cond) or any(hasParamCmd(c) for c in  r_ref.cmds) else []        
            hasNList = [Const("N")] if hasParamExpr (r_ref.cond) or any(hasParamCmd(c) for c in  r_ref.cmds) else []
            
            left1=Fun(Const("strengthenRuleByFrmL2"), [\
                Fun(Const("map2'"),[Fun(Const("lemmasFor_"+oldRuleName),[Const("N")]),Const("j"),Const("i")]), \
                Fun(Const(oldRuleName), oldhasNList)])
                
            right1=Fun(Const(r_ref.name),hasNList)
            eq1=isabelle.eq(left1,right1)
            lemmas_def=" ".join(lemma+"_def" for lemma in item["strengthen"])
            proof=isabelle.AutoProof(unfolds=[("lemmasFor_%s_def %s %s_def %s_ref")%(oldRuleName,lemmas_def,oldRuleName,oldRuleName)])
            lemma1= IsabelleLemma(name=oldRuleName+"_strengthen",assms=[], conclusion=eq1,proof=[proof]) 

            #generate lemmas on r_StrengthRel
            pred2=Fun(Const("strengthenRel"), [ \
                Fun(Const(oldRuleName+"s"),oldhasNList), \
                Fun(Const("set"), [Fun(Const("InvS"),[Const("N")])]), \
                Fun(Const(oldRuleName+"_refs"), oldhasNList),
                Const("N") \
                ])
            proof21=isabelle.blastProof(usings=["strengthenRefl"], unfolds=["%ss_def %s_refs_def %s_def %s_ref"%(oldRuleName,oldRuleName,oldRuleName,oldRuleName)])
            lemma2=IsabelleLemma(name=oldRuleName+"StrengthRel",assms=[], conclusion=pred2,proof=[proof21]) 
            predOfLemma=Fun(Const(("lemmasFor_%s"%oldRuleName)),[Const("N")])
            predOfLemma1=Fun(Const(("lemmasFor_%s"%oldRuleName+"'")),[Const("N")])
            
            #abstract r_ref
            absRule=[]
            absRules=[]
            suffix=""
            def11,lemma11,lemma21,term11,unfolds1,usings1=translateRule1(r_ref)
            deriveAllLLemmaist.append(lemma11)
            symProtAllLemmaList.append(lemma21)
            refRulesDefList.append(term11)
            deriveAllLLemmaProofUnfolds1.extend(unfolds1)
            symProtAllLemmaProofUsings2.extend(usings1)

            InvSList.append(predOfLemma)
            InvS1List.append(predOfLemma1)
            res.append(defLemma)
            '''res.append(translateRuleSet(ruleSet1))'''
            
            res.append(translateRule(r_ref))
            res.append(genRuleSymLemma(r_ref))
            res.append(def11)
            res.append(lemma1)
            res1.append(lemma2)
            
            '''for absr in absRules:
                res.append(translateRuleSet(absr))
                defA,lemmaA1,lemmaA2,termA,unfoldsA,usingsA=translateRuleSets(absr)
                res.append(defA)'''
            '''generate1. lemmas on abstraction for r_refs by json:
            2. definitions for    ABS_rules,  ABS_rules' 
            "abstract":[{"cond":{"i": false},"answer":"ABS_Idle"},{"cond":{"i": true},"answer":"ABS_Idle"}]
            lemma abs_Idle_ref
            "M \\<le> N \\<Longrightarrow> i \\<le> M \\<Longrightarrow> absTransfRule (env N) M (Idle_ref N i) = Idle_ref M i"
            "M \\<le> N \\<Longrightarrow> i > M \\<Longrightarrow> absTransfRule (env N) M (Idle_ref N i) = ABS_Idle M
            definition ABS_rules :: "nat \\<Rightarrow> rule set" where [simp]:
            "ABS_rules M \\<equiv>
            Trys M \\<union> Crits M \\<union> {ABS_Crit} \\<union> Exits M \\<union> Idle_refs M \\<union> {ABS_Idle M} \\<union> {chaos \\<triangleright> skip}"

            definition ABS_rules' :: "nat \\<Rightarrow> rule set" where [simp]:
            "ABS_rules' M \\<equiv>
            ((Trys M) \\<union> {chaos \\<triangleright> skip}) \\<union>
            ((Crits M) \\<union> {ABS_Crit}) \\<union>
            ((Exits M) \\<union> {chaos \\<triangleright> skip}) \\<union>
            ((Idle_refs M) \\<union> {ABS_Idle M})"

            lemma ABS_rules_eq_rules':
            "ABS_rules M = ABS_rules' M"
            by auto"'''
            absLemmas=[]
            unfolds=[r_ref.name]
            tmpabsRuleDefList1=[]  #for definition of rule ABS_rules
            tmpabsRuleDefListM1=[] #for lemma abs_Idle_refs
            hasNList=[Const("N")] if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds) else []
            hasMList=[Const("M")] if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds) else []

            right=Fun(Const(r_ref.name),hasMList)
            arg1=Fun(Const("env"),[Const("N")])
            arg2=Const("M")
            arg3=Fun(Const(r_ref.name),hasMList) 
            conclusion=isabelle.eq(Fun(Const("absTransfRule"),[arg1,arg2,arg3]),right)
                
            absRulesPredForAbsRules=(Fun(Const(r_ref.name+"s"),hasNList)) 
            absRuleDefList.append(absRulesPredForAbsRules)            
            tmpabsRuleDefList1.append(absRulesPredForAbsRules)
            absRulesPredForAbsRulesM=Fun(Const(r_ref.name+"s"),hasMList) 

            tmpabsRuleDefListM1.append(absRulesPredForAbsRulesM)
            assms=[Op("<=",Const("M"),Const("N")) ]
            absLemmas.append(IsabelleLemma(assms=assms,conclusion=conclusion,inLemmas=True))
                
            unfolds.append(absItem["answer"])

            absRuleDefList1.append(isabelle.Tuple(isabelle.UN(tmpabsRuleDefList1)))
            simpadds=["Let_def"]
            absLemma=IsabelleLemmas(name="abs_"+rule.name,lemmas=absLemmas,proof=[isabelle.AutoProof(unfolds=unfolds, simpadds=simpadds)])
            res.append(absLemma)
            absAllLemmaOnItemAssm=Op("<",Const("M"),Const("N"))
            absAllLemmaOnItemPred=isabelle.eq(Op("`", \
            Fun(Const("absTransfRule"),[Fun(Const("env"),[Const("N")]), \
            Const("M")]),Fun(Const(r_ref.name+"s"),hasNList)), \
                absRulesPredForAbsRulesM )
            thisUnfolds=[None if isinstance(k,isabelle.Set) else k.fun.name for k in tmpabsRuleDefListM1]
            if None in thisUnfolds:
                thisUnfolds.remove(None)
            absLemmasOnSetItemProof=isabelle.IsabelleApplyRuleProof(name="absGen",unfolds=thisUnfolds)
            absLemmasOnSetItem=IsabelleLemma(name="Abs_"+rule.name+"s", assms=[absAllLemmaOnItemAssm], conclusion=absAllLemmaOnItemPred, \
                proof=[isabelle.AutoProof(unfolds=[r_ref.name+"s", r_ref.name])]) 
            absLemmasOnSets.append(absLemmasOnSetItem)

    predOfInvS=isabelle.List(*(InvSList))
    oneLemmasType=isabelle.ListType(FunType(isabelle.nat,FunType(isabelle.nat,isabelle.formula)))
    typeOfInvS=FunType(isabelle.nat,isabelle.ListType(oneLemmasType))
    defOfInvS=Definition(name="InvS",typ=typeOfInvS,args=["N"],val=predOfInvS)
    res.append(defOfInvS)
    deriveAllLLemmaProof=[isabelle.AutoProof(unfolds=["deriveRule_def deriveForm_def deriveStmt"] \
        +deriveAllLLemmaProofUnfolds1)]
    symProtAllLemmaProof=[isabelle.AutoProof(usings=symProtAllLemmaProofUsings2+["symParaRuleInfSymRuleSet","symParaRuleInfSymRuleSet2"])]
    deriveAllLLemmas=IsabelleLemmas("deriveAllRef",deriveAllLLemmaist,proof=deriveAllLLemmaProof)
    symProtAllLemmas=IsabelleLemmas("symProtAllRef",symProtAllLemmaList,proof=symProtAllLemmaProof)
    res1.append(deriveAllLLemmas)
    res1.append(symProtAllLemmas)
    typ = FunType(isabelle.nat, isabelle.setType(isabelle.rule))
    
    def_ref_rules=Definition(name="rule_refs",typ=typ,val=isabelle.UN(refRulesDefList),args=["N"])
    res.append(def_ref_rules)
    lenOfSpec=len(strengthenSpec)
    pred2=Fun(Const("strengthenRel"), [ \
              Fun(Const("rules"),[Const("N")]), \
              Fun(Const("set"), [Fun(Const("InvS"),[Const("N")])]), \
              Fun(Const("rule_refs"), [Const("N")]),
              Const("N") \
              ])
    proof21=isabelle.IsabelleApplyRuleProof(name="strenRelUnion",unfolds=["rules", "rule_refs"])
    proof22s=[
        [isabelle.blastProof(introITag="intro",intros=["%sStrengthRel"%(getRuleOrRuleset(item))]),
        isabelle.IsabelleApplyRuleProof(name="strenRelUnion" )]
        for item in strengthenSpec[0:(lenOfSpec-2)]]

    proofs=[a for ele in proof22s for a in ele]
    lastProofs=[isabelle.blastProof(introITag="intro", \
    intros=["%sStrengthRel"%(item["ruleset"])]) \
        for item in strengthenSpec[lenOfSpec -2:(lenOfSpec)]]
    lemma2=IsabelleLemma(name="StrengthRelRules2Rule_refs",assms=[], conclusion=pred2,
    proof=[proof21]+proofs+lastProofs) 
    res1.append(lemma2) 
    absRuleDefList.append(isabelle.Set(Const("skipRule")))
    absRuleSetPred=isabelle.UN(absRuleDefList)
    absRuleDef=Definition(name="ABS_rules",typ=FunType(isabelle.nat,isabelle.setType(isabelle.rule)), \
            val=absRuleSetPred,args=["N"],is_simp=True  )  
    absRuleSetPred1=isabelle.UN(absRuleDefList1)
    absRuleDef1=Definition(name="ABS_rules'",typ=FunType(isabelle.nat,isabelle.setType(isabelle.rule)), \
            val=absRuleSetPred1,args=["N"],is_simp=True )  #ABS_rules':absRuleDef1<-absRuleSetPred1<-absRuleDefList1<-tmpabsRuleDefList1<-absRulesPredForAbsRules
    ABS_rules_eqLemmaCon=isabelle.eq(Fun(Const("ABS_rules"),[Const("M")]), \
        Fun(Const("ABS_rules'"),[Const("M")]))
    ABS_rules_eqLemma=IsabelleLemma(name="ABS_rules_eq_rules'", assms=[], \
    conclusion=ABS_rules_eqLemmaCon,proof=[isabelle.AutoProof()]) 
    absAllLemmaAssm=Op("<",Const("M"),Const("N"))
    absAllLemmaPred=isabelle.eq(Op("`", \
        Fun(Const("absTransfRule"),[Fun(Const("env"),[Const("N")]), \
        Const("M")]),Fun(Const("rule_refs"),[Const("N")])), \
             Fun(Const("ABS_rules"),[Const("M")]))
    proof1=isabelle.substProof(rules=["ABS_rules_eq_rules'"])
    proof2=isabelle.introProof(unfolds=["rule_refs", "ABS_rules'"],rules=["image_UnI"])
    ruleNames3=getAllProtRuleNames()
    ruleNames3=["Abs_"+k+"s" for  k in ruleNames3]
    ruleNames31=getAllProtRuleSetNames()
    ruleNames31=["Abs_"+k+"_refs" for  k in ruleNames31]
    proof3=isabelle.AutoProof(simpadds=ruleNames3+ruleNames31)
    absAllLemma=IsabelleLemma(name="ABS_all",assms=[absAllLemmaAssm],conclusion=absAllLemmaPred,proof= \
        [proof1,proof2,proof3])
    return defOfabsRules+res+res1+absLemmasOnSets+[absRuleDef,absRuleDef1,ABS_rules_eqLemma,absAllLemma]

'''
defOfabsRule is for one definition ABS_rs::"nat =>rule set"
defOfabsRules is a list of defOfabsRule.

lemma ABS_rules_eq_rules':
  "ABS_rules M = ABS_rules' M"
  by auto

lemma "strengthenRel (rules N)  (set (InvS N)) (rules2 N) N "
  apply(unfold rules_def rules2_def, (rule strenRelUnion)+)
  apply(blast intro: TryStrengthRel)
    apply(blast intro: CritStrengthRel)
   apply(blast intro:ExitStrengthRel)
  by(blast intro: IdleStrengthRel) 
  lemma ABS_all:
  "M < N ⟹ absTransfRule (env N) M ` rules2 N = ABS_rules M"
  apply (subst ABS_rules_eq_rules')
  unfolding rules2_def ABS_rules'_def
  apply (intro image_UnI) by auto
  '''

def genAllInvariantsPrime(prot: murphi.MurphiProtocol) -> IsabelleLemmas:
    """Generate all lemmas for primed invariants."""
    res = []
    unfoldsForsymInvsLemma = []
    lemmasForsymInvsLemma = []
    proofsForsymInvsLemma = []

    for _, val in prot.lemma_map.items():
        extLemma = extMurphiInvariant(val)
        res.append(extLemma.genLemma1())
        res.append(extLemma.genabsTransfLemma())
        res.append(extLemma.genstrengthenVsObsLemma())
        name, lemma, proof = extLemma.genSymInvsItem1()
        unfoldsForsymInvsLemma.append(name)
        lemmasForsymInvsLemma.append(lemma)
        proofsForsymInvsLemma.append(proof)
        res.append(extLemma.genSafeAndderiveForm())

    res.append(IsabelleLemmas(
        name="symInvs",
        lemmas=lemmasForsymInvsLemma,
        proof=[isabelle.AutoProof(unfolds=unfoldsForsymInvsLemma)] + proofsForsymInvsLemma
    ))

    return res


'''lemma wellFormedRules:
  "r \\<in> rules N \\<Longrightarrow> wellFormedRule (env N) N r"
  unfolding wellFormedRule.simps
  by (auto simp add: rules_def rules_simp
    symPI_Remote_Get
    ...
    
lemma absProtSim:
  assumes "M < N"
    and "M = 1"
    and "isAbstractProtInvSet absRules Is S' M env ""\\<forall>i invL f s l. l\\<le>1 \\<and> invL \\<in> set (InvS' N) \\<longrightarrow> f \\<in> set invL \\<longrightarrow>
           reachableUpTo {f'. \\<exists>f. f \\<in> (allInitSpecs N) \\<and> f' = absTransfForm (env N) M f} (ABS_rules M) i s \\<longrightarrow>
           formEval (absTransfForm (env N) M (f 0 l)) s"
    shows isParamProtInvSet  rs Is S N "\\<forall>invL f s i j. invL \\<in> set (InvS N) \\<longrightarrow> f \\<in> set invL \\<longrightarrow>
           reachableUpTo (allInitSpecs N) (rules N) k s \\<longrightarrow>
           i \\<le> N \\<longrightarrow> j \\<le> N \\<longrightarrow> formEval (f i j) s" 
  apply (rule_tac ?rs2.0 = "rules2 N" and env="env N" and S="set (InvS N)" and S'="set (InvS' N)" and M=M and absRules="ABS_rules M" in CMP1)
  subgoal for r'''

def genAllRuleSetStuff(prot: murphi.MurphiProtocol, str_data, initSpecs):
    res = []
    lemmasFor_List = []
    InvSList1 = []
    nameOflemmasFors1 = []
    for item in str_data:
        if "ruleset" in item:
            r: murphi.MurphiRuleSet = prot.ori_rule_map[item["ruleset"]]
            extRs = extMurphiRuleSet(r, item["strengthen"])
            res.append(extRs.genStrengthenLemmasDef1(item))
            res.append(extRs.genLemmastrengthenVsObsLs())
            res.append(extRs.genFitenvLemma())
            if "lemmasFor_" + item["ruleset"] not in lemmasFor_List:
                lemmasFor_List.append("lemmasFor_" + item["ruleset"])
            predOfLemma1 = Fun(Const("lemmasFor_%s'" % item["ruleset"]),
                                        [Const("N")])
            InvSList1.append(predOfLemma1)
        else:
            r: murphi.MurphiRule = prot.ori_rule_map[item["rule"]]
            extRs = extMurphiRule(r)
            res.append(extRs.genStrengthenLemmasDef1(item))
            res.append(extRs.genLemmastrengthenVsObsLs()) 
            res.append(extRs.genFitenvLemma())
            if "lemmasFor_" + item["rule"] not in lemmasFor_List:
                lemmasFor_List.append("lemmasFor_" + item["rule"])
            predOfLemma1=Fun(Const("lemmasFor_%s'" % item["rule"]),
                                      [Const("N")])
            InvSList1.append(predOfLemma1)
         
    nameOfLemmas1 = []
    for k in prot.lemma_map:
        nameOfLemmas1.append(k + "'")

    nameOflemmasFors1=[n+"'" for n in lemmasFor_List]
    predOfInvS1=isabelle.List(*(InvSList1))
    oneLemmasType=isabelle.ListType(FunType(isabelle.nat,FunType(isabelle.nat,isabelle.formula)))
    typeOfInvS=FunType(isabelle.nat,isabelle.ListType(oneLemmasType))
    defOfInvS1=Definition(name="InvS'",typ=typeOfInvS,args=["N"],val=predOfInvS1)
    res.append(defOfInvS1)
    
    assms=[Op(":",Const("r"),Fun(Const("rule_refs"),[Const("N")]))]   
    conclusion=Fun(Const("wellFormedRule") ,[Fun(Const("env"),[Const("N")]),Const("N"),Const("r")])
    simpOnSymRules1=list(r+"_refs_def" for r in prot.ori_rule_map.keys())
    simpOnSymRules2=list("sym"+r+"_ref" for r in prot.ori_rule_map.keys())
    proof=isabelle.AutoProof(simpadds=["rule_refs_def  "]+simpOnSymRules1+simpOnSymRules2)
    res.append(IsabelleLemma(name="wellFormedRule_refs",assms=assms,conclusion=conclusion,proof=[proof]))
    
    '''lemma SafeAndderiveCLemmas : 
                  "[|M < N;M = 1;l <= 1; pinvL: set (InvS' N); pf : set pinvL; l≤ 1 
     |] 
                 ==> safeForm (env N) M (pf 0 l) & deriveForm (env N) (pf  0 l)"
    unfolding InvS'_def lemmasFor_Try'_def lemmasFor_Crit'_def lemmasFor_Idle'_def lemmasFor_Exit'_def
    using SafeAndderiveFormLemma_1 apply(auto      )    
 
    done'''
    cond1=Op("<",Const("M"),Const("N"))
    cond2=Op("=",Const("M"),Const("1"))
    cond3=Op("<=",Const("l"),Const("M"))
    cond31=Op("<=",Const("k"),Const("M"))
    cond4=Op(":",Const("pinvL"),Fun(Const("set"),[(Fun(Const("InvS'"),[Const("N")]))]))
    cond5=Op(":",Const("pf"),Fun(Const("set"),[Const("pinvL")]))
    pred1=Fun(Const("safeForm"), \
            [Fun(Const("env"),[Const("N")]), Const("M"), \
            Fun(Const("pf"),[Const("k"),Const("l")])])
    pred2=Fun(Const("deriveForm"), \
            [Fun(Const("env"),[Const("N")]),   \
            Fun(Const("pf"),[Const("k"),Const("l")])])
    unfolds=["InvS'"]+nameOflemmasFors1
    usings=["SafeAndderiveForm"+n for n in nameOfLemmas1]
    res.append(IsabelleLemma(
        assms=[cond1,cond2,cond3,cond31,cond4,cond5],
        conclusion=Op("&",pred1,pred2),
        name="SafeAndderiveAll",
        proof=[isabelle.AutoProof(unfolds=unfolds,usings=usings)]))

    '''lemma rulesIsSym:
    "symProtRules' N (rules N)"
    using symProtAll rules_def symProtRulesUnion by presburger'''
    name="rulesIsSym"
    pred=Fun(Const("symProtRules'"),[Const("N"), \
        Fun(Const("rules"),[Const("N")])])
    proof=[isabelle.IsabelleApplyRuleProof(name="symProtRulesUnion, blast intro:symProtAll",unfolds=["rules"],plus="+"),
    isabelle.blastProof(unfolds=["rules"],intros=["symProtAll"],introITag="intro")]
    res.append(IsabelleLemma(assms=[],name=name,conclusion=pred,proof=proof))

    name="rule_refsIsSym"
    pred=Fun(Const("symProtRules'"),[Const("N"), \
        Fun(Const("rule_refs"),[Const("N")])])
    proof = [isabelle.IsabelleApplyRuleProof(name="symProtRulesUnion, blast intro:symProtAllRef",
                                             unfolds=["rule_refs"], plus="+"),
             isabelle.blastProof(unfolds=["rule_refs"], intros=["symProtAllRef"], introITag="intro")]
    res.append(IsabelleLemma(assms=[],name=name,conclusion=pred,proof=proof))
    
    '''lemma rules2WellTyped:
    "r \\<in> rules2 N \\<Longrightarrow> deriveRule (env N) r"
    unfolding rules2_def'''
    name="rules2WellTyped"
    assm=Op(":",Const("r"),Fun(Const("rule_refs"),[Const("N")]))
    pred=Fun(Const("deriveRule"),[ \
        Fun(Const("env"),[Const("N")]), Const("r")])
    proof=isabelle.AutoProof(unfolds=["rule_refs"],usings=["deriveAllRef"])
    res.append(IsabelleLemma(name="rule_refsWellTyped",assms=[assm],conclusion=pred,proof=[proof]))

    #generate the lemma invOnStateOfN1:
    '''"reachableUpTo (allInitSpecs N) (rule_refs N) k s ⟹
    fitEnv s (env N)"'''
    name="ReachStafitEnv"
    assm=Fun(Const("reachableUpTo"), [(Fun(Const("allInitSpecs"),[Const("N")])), \
         Fun(Const("rule_refs"), [Const("N")]), Const("k"), Const("s")] )
    conclusion=Fun(Const("fitEnv"), \
        [Const("s"), Fun(Const("env"), [Const("N")])])
    '''proof1=isabelle.IsabelleApplyRuleProof(name="invIntro", \
        rule_tac="?fs=\" (allInitSpecs N)\"  and rs=\"(rule_refs N)\" and k=\"k\"")'''
    proof1=isabelle.IsabelleApplyEruleProof(name="invIntro1")
    proof21= isabelle.IsabelleApplyRuleProof(unfolds=["fitEnv"],name="allI")
    proof22=isabelle.IsabelleApplyRuleProof(name="impI")
    proof23=isabelle.casetacProof(goal=Const("v"))
    initSpecsOnGlobal=list(filter(lambda x:x.isGlobal,initSpecs))
    initSpecsOnParam=list(filter(lambda x: not(x.isGlobal),initSpecs))
    
    proofs5=[]
    for spec in initSpecsOnGlobal:
        pred=Op("=",Const("x1"),Const("''"+spec.assignVar+"''"))
        proofs5.append(isabelle.casetacProof(pred))
        proofs5.append(spec.genInitSubgoalProof())
        proofs5.append(isabelle.AutoProof(goalNum="1"))
        proofs5.append(isabelle.AutoProof(goalNum="1"))
    proof25=isabelle.subgoalProof(fors= ["v" ,"x1"],proofs=proofs5+[isabelle.AutoProof()])
    proofs6=[]
    for spec in initSpecsOnParam:
        pred=Op("=",Const("x21"),Const("''"+spec.assignVar+"''"))
        proofs6.append(isabelle.casetacProof(pred))
        proofs6.append(spec.genInitSubgoalProof())
        proofs6.append(isabelle.AutoProof(goalNum="1"))
        proofs6.append(isabelle.AutoProof(goalNum="1"))
    proof26=isabelle.subgoalProof(fors= ["v" ,"x21","x22"],proofs=proofs6+[isabelle.AutoProof()])
    proof2=isabelle.subgoalProof(fors=["s0"],proofs=[proof21,proof22,proof23,proof25,proof26]+[isabelle.AutoProof()])
    autoIntros=["Un_iff"]+["lemma"+k+"_fitEnv" for k in prot.ori_rule_map.keys()]
    proof3=isabelle.subgoalProof(fors=["r","sk"],proofs=[isabelle.AutoProof(unfolds=["rule_refs"],introITag="intro",intros=autoIntros)])
    lemma=IsabelleLemma(assms=[assm],conclusion=conclusion,name=name,proof=[proof1,proof2,proof3])
    #generate the main lemma apply(rule_tac ?fs=" (allInitSpecs N)"  and rs="(rule_refs N)" and k="k" in invIntro)
    res.append(lemma)
    name="absProtSim1"
    assm1=Op("<",Const("M"),Const("N"))
    assm2=Op("=",Const("M"),Const("1"))
    assm3=Fun(Const("isProtObsInvSet"),[Fun(Const("ABS_rules"),[Const("M")]), \
        Op("`",Fun(Const("absTransfForm"),[Fun(Const("env"),[Const("N")]),Const("M")]), \
            Fun(Const("allInitSpecs"),[Const("N")])), \
        Fun(Const("set"),[Fun(Const("InvS'"),[Const("N")])]), Const("M"), \
        Fun(Const("env"), [Const("N")])    ])
    conclusion=Fun(Const("isParamProtInvSet"),[Fun(Const("rules"),[Const("N")]), \
        Fun(Const("allInitSpecs"),[Const("N")]), \
        Fun(Const("set"),[Fun(Const("InvS"),[Const("N")])]), Const("N")    ])
    proof1= isabelle.IsabelleApplyRuleProof(name="CMP", \
        rule_tac="?rs2.0 = \"rule_refs N\" and env=\"env N\" and S=\"set (InvS N)\" and S'=\"set (InvS' N)\" and M=M and absRules=\"ABS_rules M\"")
    proof2=isabelle.subgoalProof(fors=["r"],proofs=[isabelle.AutoProof(usings=["wellFormedRule_refs"])])
    proof3=isabelle.subgoalProof(proofs=[isabelle.AutoProof(unfolds=["InvS'"]+nameOflemmasFors1,usings=["symInvs"])])
    proof4=isabelle.subgoalProof(proofs=[isabelle.AutoProof(usings=["rulesIsSym"])])
    proof5=isabelle.subgoalProof(proofs=[isabelle.AutoProof(usings=["symPreds"])])
    proof6=isabelle.subgoalProof(proofs=[isabelle.AutoProof()])
    proof7=isabelle.subgoalProof(proofs=[isabelle.AutoProof()])
    proof8=isabelle.subgoalProof(proofs=[isabelle.AutoProof(usings=["SafeAndderiveAll"])])
    proof9=isabelle.subgoalProof(proofs=[isabelle.AutoProof(usings=["StrengthRelRules2Rule_refs"])])
    proof10=isabelle.subgoalProof(proofs=[isabelle.AutoProof(usings=["rule_refsIsSym"])])
    proof12=isabelle.subgoalProof(proofs=[isabelle.AutoProof(usings=["rule_refsWellTyped"])])
    proof13=isabelle.subgoalProof(proofs=[isabelle.AutoProof()])
    proof14=isabelle.subgoalProof(proofs=[isabelle.AutoProof(usings=["ReachStafitEnv"])])
    proof161=isabelle.AutoProof(unfolds=["InvS","InvS'"])
    proof162s=[]
    for n in lemmasFor_List:
        thisUsing="strengthenVsObsLs_"+n
        proof162s.append(isabelle.subgoalProof(fors=[],proofs=[isabelle.AutoProof(usings=[thisUsing])]))

    proof16=isabelle.subgoalProof(proofs=[proof161]+proof162s)   
    proof17s=[isabelle.IsabelleApplyRuleProof(name="equivRuleSetReflex"),
              isabelle.AutoProof(usings=["ABS_all"])]
    '''
     apply (rule equivRuleSetReflex)
    using ABS_all 
    subgoal
    unfolding InvS_def InvS'_def
    using strengthenVsObsLs_lemmasFor_Idle by auto'''

   
    '''unfolding InvS_def lemmasFor_Idle_def  
    using symInvs by auto
  subgoal
    using rulesIsSym by auto
  subgoal StrengthRelRules2Rule_refs
    using symPreds by auto
  subgoal 
    using assms(2) by auto
  subgoal
    using assms(3) by auto'''
    res.append(IsabelleLemma(name="absProtSim",assms=[assm1,assm2,assm3],conclusion=conclusion,
    proof=[proof1,proof2,proof3,proof4,proof5,proof6,proof7,proof8,proof9,proof10,proof12,proof13, \
        proof14,proof16]+proof17s))
    return res

def translateProtocol(prot: murphi.MurphiProtocol, str_data):
    defs = []
    defs.extend(translateAllEnum(prot, str_data))
    defs.extend(translateBooleans())
    defs.extend(translateEnvByStartState(prot))
    res, initSpecs = translateStartState(prot)
    defs.extend(res)
    str_data = str_data[1:]
    defs.extend(translateAllSpecs(prot)) 
    defs.extend(genSymLemmas(prot))
    defs.extend(genStrengthenLemmas(prot, str_data))
    defs.extend(genAllInvariantsPrime(prot))
    defs.extend(genAllRuleSetStuff(prot, str_data, initSpecs))
    return defs

def translateFile(filename: str, str_file: str, theory_name: str):
    """Translate protocol files to Isabelle theory file.
    
    Parameters
    ----------
    filename : str
        Name of the abstracted protocol file
    str_file: str
        Name of the strengthened protocol file
    theory_name: str
        Name of the Isabelle theory
    """
    prot = murphiparser.parse_file(filename)
    prot.addition()

    with open(str_file, "r") as spec1:
        str_data = json.load(spec1)

    with open(theory_name + ".thy", "w") as f:
        f.write(isabelle.header(theory_name))
        defs = translateProtocol(prot, str_data)
        for t in defs:
            f.write(t.export() + '\n')
        f.write("end\n")

    print("Number of rule is %d" % len(prot.ori_rule_map.items()))
