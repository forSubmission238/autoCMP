import copy
import os
import collections
import murphi
import murphiparser as parser

def trans_ref(data_dir, protocol_name):
    """Change rules before abstraction into <name>+_ref."""
    filename = '{0}/{1}/ABS{1}.m'.format(data_dir, protocol_name)
    assert os.path.exists(filename)
    prot = parser.parse_file(filename)
    for k,r in prot.ori_rule_map.items(): 
        if isinstance(r, murphi.MurphiRule):
            r.name = str(r.name) + '_ref'

        elif isinstance(r, murphi.MurphiRuleSet):
            r.rule.name = str(r.rule.name) + '_ref'

    with open('{0}/{1}/ABS_ref_{1}.m'.format(data_dir, protocol_name), 'w') as f:
        f.write(str(prot))

def json_str_gen(filename):
    """Generate the JSON file containing abstraction and strengthening instructions."""
    print('Reading file {}...'.format(filename))
    prot = parser.parse_file(filename)
    rule_dict = collections.defaultdict(dict)
    not_skip = []
    abs2ori = {}

    # Extract enum information
    enum_type = {'enum_typs':[]}
    for typ_decl in prot.types:
            if isinstance(typ_decl.typ, murphi.EnumType) and str(typ_decl.name) != 'OTHER':
                enum_type['enum_typs'].append(typ_decl.name)

    # First iteration: build the basic framework
    for k, r in prot.ori_rule_map.items(): 
        if isinstance(r, murphi.MurphiRule):
            rule_name = r.name.replace('_ref', '')
            rule_dict[rule_name].update({"rule": rule_name})
            rule_dict[rule_name].update({"strengthen": []})
            rule_dict[rule_name].update({"answer": "{}_ref".format(rule_name)})
            rule_dict[rule_name].update({"abstract": []})

        elif isinstance(r, murphi.MurphiRuleSet):
            rule_name = r.rule.name.replace('_ref','')
            if len(r.var_decls) == 1:
                rule_dict[rule_name].update({'limits': r.var_map})
                rule_dict[rule_name].update({"ruleset": rule_name})
                rule_dict[rule_name].update({"strengthen": []})
                rule_dict[rule_name].update({"answer": "{}_ref".format(rule_name)})
                rule_dict[rule_name].update({"abstract": [{"cond": {'i' : True},"answer": "{}_ref".format(rule_name)}]})

            elif len(r.var_decls) == 2:
                rule_dict[rule_name].update({'limits': r.var_map})
                rule_dict[rule_name].update({"ruleset": rule_name})
                rule_dict[rule_name].update({"strengthen": []})
                rule_dict[rule_name].update({"answer": "{}_ref".format(rule_name)})
                rule_dict[rule_name].update({"abstract": [{"cond": {r.var_decls[0].name : True, r.var_decls[1].name : True},"answer":"{}_ref".format(rule_name)}]})
                param = list(r.var_map.keys())
                abs2ori['ABS_' + rule_name + '_' + param[0]] = rule_name
                abs2ori['ABS_' + rule_name + '_' + param[1]] = rule_name
                abs2ori['ABS_' + rule_name + '_' + param[0] + '_' + param[1]] = rule_name

    # Second iteration: obtain skipRule information, and record abstracted rules
    for k, r in prot.abs_rule_map.items():
        if isinstance(r, murphi.MurphiRule):
            if r.name in abs2ori:
                rule_name = abs2ori[r.name]
            else:
                rule_name = r.name.replace('ABS_', '')
            not_skip.append(rule_name)
            param = list(rule_dict[rule_name]['limits'].keys())
            if len(param) == 1:
                cond_res = {'i': False}
            elif len(param) == 2:
                cond_res = {param[0]: False, param[1]: False}
            rule_dict[rule_name]["abstract"].append({"cond": cond_res,"answer": r.name})

        elif isinstance(r, murphi.MurphiRuleSet):
            rule_name = abs2ori[r.rule.name]
            decl = r.rule.name.split('_')[-1]
            param = list(rule_dict[rule_name]['limits'].keys())
            not_skip.append(rule_name)
            if len(r.var_decls) == 1:
                if len(param) == 2:
                    cond_res = copy.deepcopy(rule_dict[rule_name]["abstract"][0]["cond"])
                    cond_res.update({decl:False})
                    rule_dict[rule_name]["abstract"].append({"cond": cond_res,"answer":r.rule.name})
                else:
                    raise ValueError("len of param must be 2")

            elif len(r.var_decls) == 2:
                continue
        else:
             continue

    # Third iteration: add skipRule information
    for k, r in prot.ori_rule_map.items():    
        if isinstance(r,murphi.MurphiRuleSet):
            rule_name = r.rule.name.replace('_ref','')
            if rule_name not in not_skip:
                param = list(rule_dict[rule_name]['limits'].keys())
                if len(param) == 1:
                    cond_res = {'i': False}
                    rule_dict[rule_name]["abstract"].append({"cond": cond_res,"answer": "skipRule"})
                elif len(param) == 2:
                    rule_dict[rule_name]["abstract"].append({"cond": {param[0]: False, param[1]:True},"answer": "skipRule"})
                    rule_dict[rule_name]["abstract"].append({"cond": {param[0]: True, param[1]:False},"answer": "skipRule"})
                    rule_dict[rule_name]["abstract"].append({"cond": {param[0]: False, param[1]:False},"answer": "skipRule"})
    
    return enum_type, rule_dict

def inv_2forall(filename):
    """For invariants that have only one level of forall, add another level."""    
    print("Reading file \"{}\"".format(filename)) 
    prot = parser.parse_file(filename)
    for name, inv in prot.lemma_map.items():
        cnt = 0
        tmp_expr = inv.inv
        while isinstance(tmp_expr, murphi.ForallExpr):
            para_typ = tmp_expr.typ
            tmp_expr = tmp_expr.expr
            cnt += 1
        # Only one forall level, need to add another level
        if cnt == 1:
            temp_inv = murphi.MurphiInvariant(name, murphi.ForallExpr(murphi.MurphiVarDecl('m', para_typ), inv.inv))
            prot.decls.remove(prot.inv_map[name])
            prot.decls.append(temp_inv)
        else:
            prot.decls.remove(prot.inv_map[name])
            prot.decls.append(inv)
    with open(filename, 'w') as f:
        f.write(str(prot))
