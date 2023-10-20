"""Definitions for Isabelle output"""

from typing import Dict, Iterable, Optional


def indent(s, num_space, first_line=None):
    """Indent the given string by adding spaces to each line.
    
    Parameters
    ----------
    num_space : int
        Number of spaces to add to each line
    first_line : int, optional
        Number of spaces to add to first line
    """
    if s is None:
        return ""
    lines = s.split('\n')
    if first_line is None:
        return '\n'.join(' ' * num_space + line for line in lines)
    else:
        res = ' ' * first_line + lines[0]
        if len(lines) > 1:
            res += '\n' + '\n'.join(' ' * num_space + line for line in lines[1:])
        return res

class IsabelleType:
    """Base class for all Isabelle types."""
    def priority(self) -> int:
        """Priority of the type when converting to Isabelle string."""
        raise NotImplementedError

    def export(self) -> str:
        """Convert the type to Isabelle string."""
        raise NotImplementedError
    
    def is_atom(self) -> bool:
        """Whether the type is an atom."""
        raise NotImplementedError

class ConstType(IsabelleType):
    """Constant types.
    
    This includes types with parameters, e.g. 'a list, ('a, 'b) map, etc.

    """
    def __init__(self, name: str, args: Optional[Iterable[IsabelleType]]=None):
        self.name = name
        self.args = args

    def priority(self) -> int:
        return 100

    def __str__(self):
        if not self.args:
            return self.name
        elif len(self.args) == 1:
            return "%s %s" % (self.args[0], self.name)
        else:
            return "(%s) %s" % (', '.join(str(arg) for arg in self.args), self.name)

    def __repr__(self):
        if not self.args:
            return "ConstType(%s)" % self.name
        else:
            return "ConstType(%s, %s)" % (self.name, self.args)

    def export(self) -> str:
        if not self.args:
            return self.name
        elif len(self.args) == 1:
            return "%s %s" % (self.args[0].export(), self.name)
        else:
            return "(%s) %s" % (', '.join(arg.export() for arg in self.args), self.name)
    
    def is_atom(self) -> bool:
        return not self.args

class FunType(IsabelleType):
    """Function type a => b."""
    def __init__(self, domain: IsabelleType, range: IsabelleType):
        self.domain = domain
        self.range = range

    def priority(self) -> int:
        return 50

    def __str__(self):
        s1, s2 = str(self.domain), str(self.range)
        if self.domain.priority() <= self.priority():
            s1 = "(" + s1 + ")"
        if self.range.priority() < self.priority():
            s2 = "(" + s2 + ")"
        return "%s => %s" % (s1, s2)

    def __repr__(self):
        return "FunType(%s, %s)" % (repr(self.domain), repr(self.range))
    
    def export(self) -> str:
        s1, s2 = self.domain.export(), self.range.export()
        if self.domain.priority() <= self.priority():
            s1 = "(" + s1 + ")"
        if self.range.priority() < self.priority():
            s2 = "(" + s2 + ")"
        return "%s \<Rightarrow> %s" % (s1, s2)

    def is_atom(self) -> bool:
        return False

class ListType(IsabelleType):
    def __init__(self, domain: IsabelleType):
        self.domain = domain 

    def priority(self) -> int:
        return 40

    def __str__(self):
        s1 = self.domain.export()
        return "(%s) list" % (s1)

    def __repr__(self):
        return "ListType(%s)" % (repr(self.domain))
    
    def export(self) -> str:
        s1 = self.domain.export()
        return "(%s) list" % (s1)

    def is_atom(self) -> bool:
        return False

class IsabelleTerm:
    """Base class for all Isabelle terms."""
    def priority(self) -> int:
        """Priority of the term when converted to Isabelle string."""
        raise NotImplementedError

    def export(self) -> str:
        """Convert the term to Isabelle string."""
        raise NotImplementedError

class Var(IsabelleTerm):
    """Isabelle variable."""
    def __init__(self, name: str):
        self.name = name

    def priority(self) -> int:
        return 100

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Var(%s)" % self.name

    def export(self) -> str:
        return self.name

class Const(IsabelleTerm):
    """Isabelle constant."""
    def __init__(self, name):
        self.name = name

    def priority(self) -> int:
        return 100

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Const(%s)" % self.name

    def export(self) -> str:
        return self.name

class Number(IsabelleTerm):
    """Isabelle number."""
    def __init__(self, val):
        self.val = val

    def priority(self) -> int:
        return 100

    def __str__(self):
        return str(self.val)

    def __repr__(self):
        return "Number(%s)" % self.val

    def export(self) -> str:
        return str(self.val)

class String(IsabelleTerm):
    """Isabelle string."""
    def __init__(self, text):
        self.text = text

    def priority(self) -> int:
        return 100

    def __str__(self):
        return "''%s''" % self.text

    def __repr__(self):
        return "String(%s)" % self.text

    def export(self) -> str:
        return "''%s''" % self.text


NO_ASSOC, LEFT_ASSOC, RIGHT_ASSOC = 0, 1, 2

op_map_raw = {
    "==": ("\<equiv>", 2, RIGHT_ASSOC, ""),
    "=": ("=", 50, RIGHT_ASSOC, ""),
    "+": ("+", 65, LEFT_ASSOC, ""),
    "=f": ("=\<^sub>f", 50, RIGHT_ASSOC, ""),
    "|>": ("\<triangleright>", 30, NO_ASSOC, "t"),
    "||": ("||", 35, RIGHT_ASSOC, "n"),
    "&f": ("\<and>\<^sub>f", 35, RIGHT_ASSOC, "n"),
    "|f": ("\<or>\<^sub>f", 30, RIGHT_ASSOC, "n"),
    "->f": ("\<longrightarrow>\<^sub>f", 25, RIGHT_ASSOC, "n"),
    "Un": ("\<union>", 2, LEFT_ASSOC, ""),
    "&": ("\<and>", 2, LEFT_ASSOC, ""),
    "<=": ("\<le>", 2, RIGHT_ASSOC, ""),
    ">": (">", 2, RIGHT_ASSOC, ""),
    "<": ("<", 2, RIGHT_ASSOC, ""),
    ":": ("\<in>", 2, RIGHT_ASSOC, ""),
    "`": ("`", 2, RIGHT_ASSOC, "")
}

class OpInfo:
    """Information for Isabelle binary operators."""
    def __init__(self, name: str, isa_name: str, priority: int, assoc: int, spec: str):
        self.name = name
        self.isa_name = isa_name
        self.priority = priority
        self.assoc = assoc
        self.spec = spec

op_map: Dict[str, OpInfo] = dict()
for op, (isa_name, priority, assoc, spec) in op_map_raw.items():
    op_map[op] = OpInfo(op, isa_name, priority, assoc, spec)


class Op(IsabelleTerm):
    """Isabelle binary operator application."""
    def __init__(self, op: str, t1: IsabelleTerm, t2: IsabelleTerm):
        assert op in op_map, "Op: %s not found" % op
        self.op = op
        self.t1 = t1
        self.t2 = t2

    def priority(self) -> int:
        return op_map[self.op].priority

    def assoc(self) -> int:
        return op_map[self.op].assoc

    def spec(self) -> str:
        return op_map[self.op].spec

    def __str__(self):
        s1, s2 = str(self.t1), str(self.t2)
        if self.t1.priority() < self.priority() or \
            (self.t1.priority() == self.priority() and isinstance(self.t1, Op) and
             self.assoc() == RIGHT_ASSOC):
            s1 = "(" + s1 + ")"
        if self.t2.priority() < self.priority() or \
            (self.t2.priority() == self.priority() and isinstance(self.t2, Op) and
             self.assoc() == LEFT_ASSOC):
            s2 = "(" + s2 + ")"
        return "%s %s %s" % (s1, op_map[self.op].name, s2)

    def __repr__(self):
        return "Op(%s, %s, %s)" % (self.op, repr(self.t1), repr(self.t2))

    def export(self) -> str:
        s1, s2 = self.t1.export(), self.t2.export()
        if self.t1.priority() < self.priority() or \
            (self.t1.priority() == self.priority() and isinstance(self.t1, Op) and
             self.assoc() == RIGHT_ASSOC):
            s1 = "(" + s1 + ")"
        if self.t2.priority() < self.priority() or \
            (self.t2.priority() == self.priority() and isinstance(self.t2, Op) and
             self.assoc() == LEFT_ASSOC):
            s2 = "(" + s2 + ")"
        if self.spec() == "n":
            return "%s %s\n%s" % (s1, op_map[self.op].isa_name, s2)
        elif self.spec() == "t":
            return "\n%s\n%s\n%s" % (indent(s1, 1), op_map[self.op].isa_name, indent(s2, 1))
        else:
            return "%s %s %s" % (s1, op_map[self.op].isa_name, s2)

uop_map_raw = {
    "~": ("\<not>", 40),
    "~f": ("\<not>\<^sub>f", 40),
}

class UOpInfo:
    """Information for Isabelle unary operators."""
    def __init__(self, name: str, isa_name: str, priority: int):
        self.name = name
        self.isa_name = isa_name
        self.priority = priority

uop_map: Dict[str, UOpInfo] = dict()
for uop, (isa_name, priority) in uop_map_raw.items():
    uop_map[uop] = UOpInfo(uop, isa_name, priority)

class UOp(IsabelleTerm):
    """Isabelle unary operator application"""
    def __init__(self, op: str, t: IsabelleTerm):
        assert op in uop_map, "UOp: %s not found" % op
        self.op = op
        self.t = t

    def priority(self) -> int:
        return uop_map[self.op].priority

    def __str__(self):
        s = str(self.t)
        if self.t.priority() < self.priority():
            s = "(" + s + ")"
        return "%s %s" % (uop_map[self.op].name, s)

    def __repr__(self):
        return "UOp(%s, %s)" % (self.op, repr(self.t))

    def export(self) -> str:
        s = self.t.export()
        if self.t.priority() < self.priority():
            s = "(" + s + ")"
        return "%s %s" % (uop_map[self.op].isa_name, s)

class Fun(IsabelleTerm):
    """Isabelle function application"""
    def __init__(self, fun: IsabelleTerm, args: Iterable[IsabelleTerm]):
        assert isinstance(fun, IsabelleTerm)
        assert isinstance(args, list)
        self.fun = fun
        self.args = tuple(args)

    def priority(self) -> int:
        return 90

    def __str__(self):
        str_args = []
        for arg in (self.fun,) + self.args:
            str_arg = str(arg)
            if arg.priority() <= self.priority():
                str_arg = "(" + str_arg + ")"
            str_args.append(str_arg)
        
        return " ".join(str_args)

    def __repr__(self):
        return "Fun(%s, %s)" % (self.fun, self.args)

    def export(self) -> str:
        str_args = []
        for arg in (self.fun,) + self.args:
            str_arg = arg.export()
            if arg.priority() <= self.priority():
                str_arg = "(" + str_arg + ")"
            str_args.append(str_arg)
        
        return " ".join(str_args)

class Tuple(IsabelleTerm):
    """Isabelle tuple."""
    def __init__(self, *args: IsabelleTerm):
        assert all(isinstance(arg, IsabelleTerm) for arg in args)
        self.args = tuple(args)

    def priority(self):
        return 100

    def __str__(self):
        return "(%s)" % (', '.join(str(arg) for arg in self.args))

    def __repr__(self):
        return "Tuple(%s)" % (', '.join(repr(arg) for arg in self.args))

    def export(self):
        return "(%s)" % (', '.join(arg.export() for arg in self.args))

class Set(IsabelleTerm):
    """Isabelle set."""
    def __init__(self, *args: IsabelleTerm):
        assert all(isinstance(arg, IsabelleTerm) for arg in args)
        self.args = tuple(args)

    def priority(self) -> int:
        return 100

    def __str__(self):
        return "{%s}" % (', '.join(str(arg) for arg in self.args))

    def __repr__(self):
        return "Set(%s)" % (', '.join(repr(arg) for arg in self.args))

    def export(self) -> str:
        return "{%s}" % (', '.join(arg.export() for arg in self.args))

class CollectSet(IsabelleTerm):
    """Define set by collection in Isabelle."""
    def __init__(self, bound_var: str, body: IsabelleTerm):
        self.bound_var = bound_var
        self.body = body

    def priority(self) -> int:
        return 100

    def __str__(self):
        return "{%s. %s}" % (self.bound_var, self.body)

    def __repr__(self):
        return "CollectSet(%s, %s)" % (self.bound_var, repr(self.body))

    def export(self) -> str:
        return "{%s. %s}" % (self.bound_var, self.body.export())

class List(IsabelleTerm):
    """Isabelle list."""
    def __init__(self, *args: IsabelleTerm):
        assert all(isinstance(arg, IsabelleTerm) for arg in args)
        self.args = tuple(args)

    def priority(self) -> int:
        return 100

    def __str__(self):
        return "[%s]" % (', '.join(str(arg) for arg in self.args))

    def __repr__(self):
        return "List(%s)" % (', '.join(repr(arg) for arg in self.args))

    def export(self) -> str:
        return "[%s]" % (', '.join(arg.export() for arg in self.args))

quant_op_map = {
    "%": "\<lambda>",
    "all": "\<forall>",
    "ex": "\<exists>",
    "all_f": "\<forall>\<^sub>f",
    "ex_f": "\<exists>\<^sub>f",
}

class Quant(IsabelleTerm):
    """Isabelle quantification term."""
    def __init__(self, quant_op: str, bound_var: str, t: IsabelleTerm):
        assert quant_op in quant_op_map, "Quant: %s not found" % quant_op
        self.quant_op = quant_op
        self.bound_var = bound_var
        self.t = t

    def priority(self) -> int:
        return 10

    def __str__(self):
        return "%s%s. %s" % (quant_op_map[self.quant_op], self.bound_var, self.t.export())

    def __repr__(self):
        return "Quant(%s, %s, %s)" % (self.quant_op, self.bound_var, repr(self.t))

    def export(self) -> str:
        return "%s%s. %s" % (quant_op_map[self.quant_op], self.bound_var, self.t.export())

ite_map = {
    "iteStm": ("IF", "DO", "ELSE", "FI", "n"),
    "isabelleIte": ("if", "then", "else")
}

class ITE(IsabelleTerm):
    """Isabelle if-then-else term"""
    def __init__(self, ite_name: str, b: IsabelleTerm, t1: IsabelleTerm, t2: IsabelleTerm):
        self.ite_name = ite_name
        assert self.ite_name in ite_map
        self.b = b
        self.t1 = t1
        self.t2 = t2

    def priority(self) -> int:
        return 10

    def __str__(self):
        str_if, str_do, str_else, str_fi, _ = ite_map[self.ite_name]
        return "%s %s %s %s %s %s %s" % (str_if, self.b, str_do, self.t1, str_else, self.t2, str_fi)

    def __repr__(self):
        return "ITE(%s, %s, %s, %s)" % (self.ite_name, repr(self.b), repr(self.t1), repr(self.t2))

    def export(self) -> str:
        str_if, str_do, str_else, str_fi, spec = ite_map[self.ite_name]
        if spec == 'n':
            res = "%s %s %s\n" % (str_if, self.b.export(), str_do)
            res += indent(self.t1.export(), 2) + "\n"
            res += "%s\n" % str_else
            res += indent(self.t2.export(), 2) + "\n"
            res += str_fi
            return res
        else:
            raise NotImplementedError

 
class IsabelleITE(IsabelleTerm):
    def __init__(self, ite_name: str, b: IsabelleTerm, t1: IsabelleTerm, t2: IsabelleTerm):
        self.ite_name = ite_name
        assert self.ite_name in ite_map
        self.b = b
        self.t1 = t1
        self.t2 = t2

    def priority(self) -> int:
        return 10

    def __str__(self):
        str_if, str_then, str_else = ite_map[self.ite_name]
        return "%s %s %s %s %s %s " % (str_if, self.b, str_then, self.t1, str_else, self.t2)

    def __repr__(self):
        str_if, str_then, str_else = ite_map[self.ite_name]
        return "%s %s %s %s %s %s %s" % (str_if, self.b, str_then, self.t1, str_else, self.t2)

    def export(self) -> str:
        str_if, str_then, str_else = ite_map[self.ite_name]
        res = "%s %s" % (str_if, self.b.export())
        res += " %s %s" % (str_then, self.t1.export())
        res += " %s %s" % (str_else, self.t2.export())
        return res
        

class IsabelleDecl:
    """Base class for Isabelle declarations."""
    def export(self) -> str:
        """Convert declaration to string."""
        raise NotImplementedError


class Definition(IsabelleDecl):
    """Isabelle definition."""
    def __init__(self, name: str, typ: IsabelleType, val: IsabelleTerm, *,
                 args: Optional[Iterable[IsabelleTerm]] = None,
                 is_simp: bool = False, is_equiv: bool = False):
        self.name = name
        self.typ = typ
        self.val = val
        if args is None:
            args = tuple()
        self.args = tuple(args)
        self.is_simp = is_simp
        self.is_equiv = is_equiv
        if self.is_equiv:
            self.equiv_op = "=="
        else:
            self.equiv_op = "="
        self.definition = Op(self.equiv_op, Fun(Var(self.name), [Var(arg) for arg in self.args]), self.val)

    def __str__(self):
        res = "definition %s :: \"%s\" where%s\n" % (self.name, self.typ, " [simp]:" if self.is_simp else "")
        res += indent(str(self.definition), 2)
        return res

    def __repr__(self):
        if self.is_simp:
            return "Definition(%s, %s, %s, is_simp=True)" % (self.name, repr(self.typ), repr(self.val))
        else:
            return "Definition(%s, %s, %s)" % (self.name, repr(self.typ), repr(self.val))

    def export(self) -> str:
        res = "definition %s :: \"%s\" where%s\n" % (
            self.name, self.typ.export(), " [simp]:" if self.is_simp else "")
        res += indent("\"" + self.definition.export() + "\"", 2) + "\n"
        return res

class Proof:
    """Base class of Isabelle proofs."""
    pass

class IsabelleLemma(IsabelleDecl):
    """Isabelle lemma."""
    def __init__(self, assms: Iterable[IsabelleTerm], conclusion: IsabelleTerm, *,
                 attribs: Optional[Iterable[str]] = None,
                 name: Optional[str] = None,
                 proof: Optional[Iterable[Proof]] = None,
                 inLemmas: bool = False):
        self.name = name
        self.assms = tuple(assms)
        self.conclusion = conclusion
        if attribs is None:
            attribs = tuple()
        self.attribs = tuple(attribs)
        if proof is None:
            proof = tuple()
        self.proof = tuple(proof)
        self.inLemmas = inLemmas

    def __str__(self):
        assmPart = "" if len(self.assms) == 0 else \
                    '[|' + (';'.join(str(assm) for assm in self.assms)) + '|]'
        concPart = str(self.conclusion)
        attribStr = "" if len(self.attribs) == 0 else \
                    "[%s]" % (",".join(attrib for attrib in self.attribs))
        if not self.inLemmas:
            res = "lemma %s %s: \n  \"%s%s%s\"\n%s\n  done\n" % ( \
                    self.name, attribStr,
                    assmPart,
                    " ==> " if len(self.assms) > 0 else "", concPart.lstrip(),
                    "" if len(self.proof) == 0 else indent('\n'.join(str(proof) for proof in self.proof), 2)
                )
        else:
            res = "\"%s%s%s\"\n  %s\n" % (
                    assmPart,
                    " ==> " if len(self.assms) > 0 else "", concPart.lstrip(),
                    "" if len(self.proof) == 0 else indent('\n'.join(str(proof) for proof in self.proof), 2)
                )
        return res

    def __repr__(self): 
        return "IsabelleLemma(%s, %s, %s, %s,%s)" % \
            (self.name, repr(self.assms), repr(self.conclusion),
             repr(self.attribs),repr(self.proof))

    def export(self):
        assmPart = "" if len(self.assms) == 0 else \
                '[|' + (';'.join(str(assm) for assm in self.assms)) + '|]'
        concPart = str(self.conclusion)
        attribStr = "" if len(self.attribs) == 0 else \
                    "[%s]" % (",".join(attrib for attrib in self.attribs))
        if not self.inLemmas:
            res = "lemma %s %s: \n  \"%s%s%s\"\n%s\n  done\n" % (
                    self.name, attribStr,
                    assmPart, " ==> " if len(self.assms)>0 else "", concPart.lstrip(),
                    "" if len(self.proof) == 0 else indent('\n'.join(str(proof) for proof in self.proof), 2)
                )
        else:
            res = "\"%s%s%s\"\n %s\n" % (
                    assmPart, " ==> " if len(self.assms)>0 else "", concPart.lstrip(),
                    "" if len(self.proof) == 0 else indent('\n'.join(str(proof) for proof in self.proof), 2)
                )
        return res
    

class IsabelleLemmas(IsabelleDecl):
    """Multiple lemmas in one declaration."""
    def __init__(self, name: str, lemmas: Iterable[IsabelleLemma], proof: Iterable[Proof]):
        self.name = name
        self.lemmas = tuple(lemmas)
        self.proof = tuple(proof)

    def __str__(self):
        res = "lemma %s : \n%s\n%s\n  done\n" % (
                self.name,
                indent('\n'.join(str(lemma).strip() for lemma in self.lemmas), 2),
                indent('\n'.join(str(proof) for proof in self.proof), 2)
            )
        return res

    def __repr__(self): 
            return "IsabelleLemmas(%s, %s, %s)" % (self.name, repr(self.lemmas), repr(self.proof))

    def export(self):
        res = "lemma %s : \n%s\n%s\n  done\n" % (
                self.name,
                indent('\n'.join(str(lemma).strip() for lemma in self.lemmas), 2),
                indent('\n'.join(str(proof) for proof in self.proof), 2)
            )
        return res

class IsabelleApplyRuleProof(Proof):
    """Isabelle apply tactic."""
    def __init__(self, name: str, *, unfolds=[], usings=[],plus=None,rule_tac=None):
        self.name = name
        self.usings = usings
        self.unfolds = unfolds
        self.plus = plus
        self.rule_tac = rule_tac

    def __str__(self):
        unfoldStr = '' if len(self.unfolds) == 0 else \
            "unfolding " + (" ".join(un + "_def" for un in self.unfolds) + "\n")

        usingStr = '' if len(self.usings) == 0 else \
            "using " + (" ".join(us for us in self.usings) + "\n") 

        plusStr = '' if self.plus is None else "+"

        if self.rule_tac is None:
            res = "apply (rule %s)" % self.name
        else:
            res = "apply (rule_tac " + self.rule_tac + " in " + self.name + ")"
        return unfoldStr + usingStr + res + plusStr

    def __repr__(self): 
        return "ApplyRule(%s, %s, %s, %s)" % \
            (self.name, repr(self.unfolds), repr(self.usings), repr(self.plus))

class IsabelleApplyEruleProof(Proof):
    def __init__(self, name, *, unfolds=[], usings=[],plus=None,rule_tac=None):
        self.name = name
        self.usings = usings
        self.unfolds = unfolds
        self.plus = plus
        self.rule_tac = rule_tac

    def __str__(self):
        unfoldStr = '' if len(self.unfolds) == 0 else \
            "unfolding " + (" ".join(un + "_def" for un in self.unfolds) + "\n")

        usingStr = '' if len(self.usings) == 0 else \
            "using " + (" ".join(us  for us in self.usings) + "\n") 

        plusStr = '' if self.plus is None else "+" 

        if self.rule_tac is None:
            res = "apply (erule %s)" % self.name
        else:
            res = "apply (erule_tac " + self.rule_tac + " in " + self.name + ")"
        return unfoldStr + usingStr + res + plusStr

    def __repr__(self): 
        return "ApplyErule(%s, %s, %s, %s)" % \
            (self.name, repr(self.unfolds), repr(self.usings), repr(self.plus))

class GenericProof(Proof):
    def __init__(self, tactic_name: str, *, unfolds=[], usings=[], introITag=None,
                 intros=[],simpadds=[], simpdels=[],plus=None,goalNum=None): 
        self.tactic_name = tactic_name
        self.usings=usings
        self.unfolds=unfolds
        self.plus=plus
        self.intros =intros 
        self.simpadds=simpadds
        self.simpdels=simpdels
        self.introITag=introITag
        self.goalNum=goalNum

    def __str__(self):
        unfoldStr='' if len(self.unfolds)==0 else \
            "unfolding " + (" ".join(str(un)+"_def" for un in self.unfolds) + "\n")

        usingStr = '' if len(self.usings)==0 else \
            "using " + (" ".join(us  for us in self.usings) + "\n") 

        plusStr = '' if self.plus is None else "+" 
        introStr = '' if self.introITag is None else (self.introITag+": "+(" ".join(str(intro) for intro in self.intros)))

        simpdelStr = '' if len(self.simpdels)==0 else ("simp del: " + (" ".join(str(del0) for del0 in self.simpdels) ))

        simpaddStr = '' if len(self.simpadds)==0 else ('simp add: ' + (" ".join(str(add) for add in self.simpadds)) )

        goalStr = ""  if (self.goalNum==None) else "[%s]"%self.goalNum
        
        if introStr or simpaddStr or simpdelStr or goalStr:
            res= "apply (%s%s%s%s)%s"   % \
            ( self.tactic_name, '' if introStr=='' else " " + introStr, \
                '' if simpaddStr=='' else " " + simpaddStr, \
                '' if simpdelStr=='' else " " + simpdelStr, \
                '' if goalStr=='' else goalStr)
        else:
            res = "apply %s" % self.tactic_name

        return unfoldStr + usingStr + res + plusStr

    def __repr__(self): 
        return "%s ( %s, %s, %s,%s,%s,%s)" % \
            (self.tactic_name, repr(self.unfolds),  \
            repr(self.usings),repr(self.plus),repr(self.intros), \
            repr(self.simpadds),repr(self.simpdels))

class AutoProof(GenericProof):
    def __init__(self, **kwargs):
        super().__init__("auto", **kwargs)

class blastProof(GenericProof):
    def __init__(self, **kwargs):
        super().__init__("blast", **kwargs)

class introProof(Proof):
    def __init__(self, *, unfolds=[], usings=[], 
        intros=[],plus=None): 
        self.unfolds=unfolds
        self.plus=plus
        self.intros =intros 
        self.usings=usings

    def __str__(self):
        unfoldStr = '' if len(self.unfolds)==0 else \
            "unfolding " + (" ".join(str(un)+"_def" for un in self.unfolds) + "\n")

        usingStr = '' if len(self.usings)==0 else \
            "using " + (" ".join(us  for us in self.usings) + "\n") 

        plusStr = '' if self.plus==None else "+" 
        introStr = '' if   self.intros==[] else (" "+(" ".join(str(intro) for intro in self.intros)))

        res= "apply (intro%s)%s"   % \
            ( '' if introStr=='' else " " + introStr, \
                '' if plusStr=='' else plusStr)
        return unfoldStr + usingStr + res

    def __repr__(self): 
        unfoldStr='' if len(self.unfolds)==0 else \
            "unfolding " + (" ".join(str(un)+"_def" for un in self.unfolds) + "\n")

        usingStr = '' if len(self.usings)==0 else \
            "using " + (" ".join(us  for us in self.usings) + "\n") 

        plusStr = '' if self.plus==None else "+" 
        introStr = '' if self.introITag==None else (" "+(" ".join(str(intro) for intro in self.intros)))

        res= "apply (intro%s)%s"   % \
            ( '' if introStr=='' else " " + introStr, \
                '' if plusStr=='' else plusStr)

        return unfoldStr + usingStr + res

class presburgerProof(Proof):
    def __init__(self,   unfolds=[], usings=[], introITag=None,
        intros=[],simpadds=[], simpdels=[],plus=None): 
        self.usings=usings
        self.unfolds=unfolds
        self.plus=plus
        self.intros =intros 
        self.simpadds=simpadds
        self.simpdels=simpdels
        self.introITag=introITag

    def __str__(self):
        unfoldStr='' if len(self.unfolds)==0 else \
            "unfolding " + (" ".join(str(un)+"_def" for un in self.unfolds) + "\n")

        usingStr = '' if len(self.usings)==0 else \
            "using " + (" ".join(us  for us in self.usings) + "\n") 

        plusStr = '' if self.plus==None else "+" 
        
        introStr = '' if   self.introITag==None else (self.introITag+" "+(" ".join(str(intro) for intro in self.intros)))

        simpdelStr = '' if len(self.simpdels)==0 else ("del: " + (" ".join(str(del0) for del0 in self.simpdels) ))
        
        simpaddStr = '' if len(self.simpadds)==0 else ('simp add: ' + (" ".join(str(add) for add in self.simpadds)) )
        
        res= "apply (presburger%s%s%s)%s"   % \
            ( '' if introStr=='' else " " + introStr, \
                '' if simpaddStr=='' else " " + simpaddStr, \
                '' if simpdelStr=='' else " " + simpdelStr, \
                '' if plusStr=='' else plusStr)
         
        return unfoldStr + usingStr + res

    def __repr__(self): 
        return "auto( %s, %s, %s,%s,%s,%s)" % \
            (repr(self.unfolds),  \
            repr(self.usings),repr(self.plus),repr(self.intros), \
            repr(self.simpadds),repr(self.simpdels))

class substProof(Proof):
    def __init__(self,  name, unfolds=[], usings=[], introITag=None,
        intros=[],simpadds=[], simpdels=[],plus=None): 
        self.name=name
        self.usings=usings
        self.unfolds=unfolds
        self.plus=plus
        self.intros =intros 
        self.simpadds=simpadds
        self.simpdels=simpdels
        self.introITag=introITag


    def __str__(self):
        unfoldStr='' if len(self.unfolds)==0 else \
            "unfolding " + (" ".join(str(un)+"_def" for un in self.unfolds) + "\n")

        usingStr = '' if len(self.usings)==0 else \
            "using " + (" ".join(us  for us in self.usings) + "\n") 

        plusStr='' if self.plus==None else "+"

        introStr='' if   self.introITag==None else (self.introITag+" "+(" ".join(str(intro) for intro in self.intros)))

        simpdelStr='' if len(self.simpdels)==0 else ("del: " + (" ".join(str(del0) for del0 in self.simpdels) ))

        simpaddStr='' if len(self.simpadds)==0 else ('simp add: ' + (" ".join(str(add) for add in self.simpadds)) )
                 
        # res= "apply (subst %s  %s %s   %s %s)%s"   % \
        #     (self.name, introStr, destStr, simpaddStr, simpdelStr,plusStr)
        res= "apply (subst%s%s%s%s)%s"   % \
            ( '' if self.name=='' else " " + self.name, \
                '' if introStr=='' else " " + introStr, \
                '' if simpaddStr=='' else " " + simpaddStr, \
                '' if simpdelStr=='' else " " + simpdelStr, \
                '' if plusStr=='' else plusStr)

        # return unfoldStr+' '+usingStr+' '+res
        return unfoldStr + usingStr + res

    def __repr__(self): 
        return "subst(%s %s, %s, %s,%s,%s,%s)" % \
            (self.name,repr(self.unfolds),  \
            repr(self.usings),repr(self.plus),repr(self.intros), \
            repr(self.simpadds),repr(self.simpdels))

class subgoalProof(Proof):
    def __init__(self,fors=None,proofs=None): 
        self.fors=fors
        self.proofs=proofs 

    def __str__(self):
        res1="subgoal for %s\n" % (" ".join(s for s in self.fors)) if self.fors else "subgoal"
        res2=indent("\n".join(str(s) for s in self.proofs), 2)
        res3="\n  done\n"
        return(res1+res2+res3)

    def export(self):
        res1="subgoal for %s\n" % (" ".join(s for s in self.fors)) if self.fors else "subgoal"
        res2=indent("\n".join(str(s) for s in self.proofs), 2)
        res3="\n  done\n"
        return(res1+res2+res3)


class subgoaltacProof(Proof):
    def __init__(self,goal): 
        self.goal=goal

    def __str__(self):
        res1="apply (subgoal_tac  \"%s\")\n"%(str(self.goal))  
        return(res1)

    def export(self):
        res1="apply (subgoal_tac  \"%s\")\n"%(str(self.goal))  
        return(res1)

class casetacProof(Proof):
    def __init__(self,goal): 
        self.goal=goal

    def __str__(self):
        res1="apply (case_tac   \"%s\")\n"%(str(self.goal))  
        return(res1)

    def export(self):
        res1="apply (case_tac   \"%s\")\n"%(str(self.goal))  
        return(res1)

class primRec: 
    def __init__(self,name,typ,eqs): 
        self.name=name
        self.typ=typ
        self.eqs=eqs

    def __str__(self):
        res="primrec %s :: \"%s\" where\n%s\n"% \
            (self.name, self.typ, indent(" |\n".join("\"" + eq.export() + "\"" for eq in self.eqs), 2))
        return(res)

    def __repr__(self):
        res="primrec %s :: \"%s\" where\n%s\n"% \
            (self.name, self.typ, indent(" |\n".join("\"" + str(eq) + "\"" for eq in self.eqs), 2))
        return(res)

    def export(self):
        res="primrec %s :: \"%s\" where\n%s\n"% \
            (self.name, self.typ, indent(" |\n".join("\"" + eq.export() + "\"" for eq in self.eqs), 2))
        return(res)



'''primrec env :: "nat \<Rightarrow> envType" where
  "env N (Para n i) =
   (if n = ''Sta.n'' \<and> i \<le> N then enumType else anyType)"
| "env N (Ident n) =
   (if n = ''Sta.x'' then boolType else anyType)"
| "env N dontCareVar = anyType"'''


nat = ConstType("nat")
formula = ConstType("formula")
rule = ConstType("rule")
scalarValueType = ConstType("scalrValueType")
def setType(t):
    return(ConstType(str(t)+" set"))

def enum(cl, v):
    return Fun(Const("enum"), [String(cl), String(v)])

isaTrue = Const("True")
isaFalse = Const("False")

def boolV(v):
    return Fun(Const("boolV"), [isaTrue if v else isaFalse])

def index(s):
    return Fun(Const("Const"), [Fun(Const("index"), [Var(s)])])

def other(n):
    return Fun(Const("Const"), [Fun(Const("index"), [Op("+", Var(n), Number(1))])])

def allF(v, t, n):
    return Fun(Quant("all_f", v, t), [Var(n)])

def exF(v, t, n):
    return Fun(Quant("ex_f", v, t), [Var(n)])

def allExclF(v, t, j, n):
    return Fun(Const("forallFormExcl"), [Quant("%", v, t), Var(j), Var(n)])

def iteF(b, s1, s2):
    return Fun(Const("iteForm"), [b, s1, s2])

def eqF(t1, t2):
    return Op("=f", t1, t2)

def eq(t1, t2):
    return Op("=", t1, t2)

def andF(args):
    if len(args) == 1:
        return args[0]
    else:
        return Op("&f", args[0], andF(args[1:]))

def orF(args):
    if len(args) == 1:
        return args[0]
    else:
        return Op("|f", args[0], orF(args[1:]))

def impF(args):
    if len(args) == 1:
        return args[0]
    else:
        return Op("->f", args[0], impF(args[1:]))

def addE(args):
    if len(args) == 1:
        return args[0]
    else:
        return Op("+", args[0], addE(args[1:]))

def notF(arg):
    return UOp("~f", arg)

def UN(args):
    if len(args) == 1:
        return args[0]
    else:
        return Op("Un", args[0], UN(args[1:]))

def UNLeft(args):
    if len(args) == 1:
        return args[0]
    else:
        return Op("Un", UNLeft(args[0:(len(args)-1)]),args[-1])

def IVar(t):
    return Fun(Const("IVar"), [t])

def Ident(s):
    return Fun(Const("Ident"), [String(s)])

def Para(s, v):
    return Fun(Const("Para"), [String(s), Var(v)])

def boolE(v):
    if v:
        return Fun(Const("Const"), [Const("true")])
    else:
        return Fun(Const("Const"), [Const("false")])

def ConstE(s):
    return Fun(Const("Const"), [Const(s)])

def assignS(v, e):
    assert isinstance(v, IsabelleTerm) and isinstance(e, IsabelleTerm)
    return Fun(Const("assign"), [Tuple(v, e)])

def parallelS(args):
    if len(args) == 1:
        return args[0]
    else:
        return Op("||", args[0], parallelS(args[1:]))

def forallS(v, cmd, n):
    return Fun(Const("forallStm"), [Quant("%", v, cmd), Var(n)])

def forallExclS(v, cmd, j, n):
    return Fun(Const("forallStmExcl"), [Quant("%", v, cmd), Var(j), Var(n)])

def iteS(b, c1, c2):
    return ITE("iteStm", b, c1, c2)

def ruleS(conds, stmts):
    return Op("|>", andF(conds), parallelS(stmts))

def enum_def(cl, v):
    return Definition(v, scalarValueType, enum(cl, v), is_simp=True, is_equiv=True)

def header(thy_name):
    return """
theory %s
  imports ECMP
begin

""" % thy_name

test_data = [
    enum_def("control", "I"),
    enum_def("control", "S"),
    enum_def("control", "E"),
    enum_def("control", "Empty"),
    enum_def("control", "ReqS"),
    enum_def("control", "ReqE"),
    enum_def("control", "Inv"),
    enum_def("control", "InvAck"),
    enum_def("control", "GntS"),
    enum_def("control", "GntE"),
    Definition("true", scalarValueType, boolV(True), is_simp=True, is_equiv=True),
    Definition("false", scalarValueType, boolV(True), is_simp=True, is_equiv=True),
    Definition(
        "initSpec0",
        FunType(nat, formula),
        allF("i", eqF(IVar(Para("n", "i")), ConstE("I")), "N"),
        args=["N"],
        is_simp=True, is_equiv=True
    ),
    Definition(
        "RecvGntE",
        FunType(nat, rule),
        ruleS([eqF(IVar(Para("Chan2.Cmd", "i")), ConstE("GntE"))],
              [assignS(Para("Cache.State", "i"), ConstE("E")),
               assignS(Para("Chan2.Cmd", "i"), ConstE("Empty"))]),
        args=["i"],
        is_equiv=True
    ),
    Definition(
        "SendGntE",
        FunType(nat, FunType(nat, rule)),
        ruleS([eqF(IVar(Ident("CurCmd")), ConstE("ReqE")),
               eqF(IVar(Ident("CurPtr")), index("i")),
               eqF(IVar(Para("Chan2.Cmd", "i")), ConstE("Empty")),
               eqF(IVar(Ident("ExGntd")), boolE(False)),
               allF("j", eqF(IVar(Para("ShrSet", "j")), boolE(False)), "N")],
              [assignS(Para("Chan2.Cmd", "i"), ConstE("GntE")),
               assignS(Para("ShrSet", "i"), boolE(True)),
               assignS(Ident("ExGntd"), boolE(True)),
               assignS(Ident("CurCmd"), ConstE("Empty"))]),
        args=["N", "i"],
        is_equiv=True
    ),
    IsabelleLemma([], 
        Fun(Const("symPredSet'"), [Const("N"), Const("{initSpec1}")]),
        attribs=["intro"],
        name="symPreds1",
        proof=[
            AutoProof(unfolds=["symPredSet'"]),
            AutoProof(unfolds=["symPredSet'"])
        ]
    ),
    CollectSet('x', Fun(Var('P'), [Var('x')])),
]

if __name__ == "__main__":
    print(type((arg+1 for arg in [1,2,3])))
    with open("IsabelleTest.thy", "w") as f:
        f.write(header("IsabelleTest"))
        for t in test_data:
            #print(str(t))
            f.write(t.export())


#lemma symPreds1 [intro]:
#  "symPredSet' N {initSpec1}"
#  unfolding symPredSet'_def by auto