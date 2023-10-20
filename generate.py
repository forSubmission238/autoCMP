import copy
import json
import os
import collections
import murphi
import murphiparser as parser

#将没抽象的规则名字全改为name+_ref
def trans_ref(data_dir, protocol_name):
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
    print('Reading file {}...'.format(filename))
    prot = parser.parse_file(filename)
    rule_dict = collections.defaultdict(dict)
    not_skip = []
    abs2ori = {}

    #提取enum信息
    enum_type = {'enum_typs':[]}
    for typ_decl in prot.types:
            if isinstance(typ_decl.typ, murphi.EnumType) and str(typ_decl.name) != 'OTHER':
                enum_type['enum_typs'].append(typ_decl.name)

    #第一次遍历,建立框架
    for k,r in prot.ori_rule_map.items(): 
        if isinstance(r, murphi.MurphiRule):
            rule_name = r.name.replace('_ref','')
            rule_dict[rule_name].update({"rule":rule_name})
            rule_dict[rule_name].update({"strengthen":[]})
            rule_dict[rule_name].update({"answer":"{}_ref".format(rule_name)})
            rule_dict[rule_name].update({"abstract":[]})

        elif isinstance(r,murphi.MurphiRuleSet):
            rule_name = r.rule.name.replace('_ref','')
            if len(r.var_decls)==1:
                rule_dict[rule_name].update({'limits':r.var_map})
                rule_dict[rule_name].update({"ruleset":rule_name})
                rule_dict[rule_name].update({"strengthen":[]})
                rule_dict[rule_name].update({"answer":"{}_ref".format(rule_name)})
                # rule_dict[rule_name].update({"abstract":[{"cond": {r.var_decls[0].name : True},"answer":"{}_ref".format(rule_name)}]})
                rule_dict[rule_name].update({"abstract":[{"cond": {'i' : True},"answer":"{}_ref".format(rule_name)}]})

            elif len(r.var_decls)==2:
                rule_dict[rule_name].update({'limits':r.var_map})
                rule_dict[rule_name].update({"ruleset":rule_name})
                rule_dict[rule_name].update({"strengthen":[]})
                rule_dict[rule_name].update({"answer":"{}_ref".format(rule_name)})
                rule_dict[rule_name].update({"abstract":[{"cond": {r.var_decls[0].name : True, r.var_decls[1].name : True},"answer":"{}_ref".format(rule_name)}]})
                param = list(r.var_map.keys())
                abs2ori['ABS_'+rule_name+'_'+param[0]] = rule_name
                abs2ori['ABS_'+rule_name+'_'+param[1]] = rule_name
                abs2ori['ABS_'+rule_name+'_'+param[0]+'_'+param[1]] = rule_name
    # print(abs2ori)

    #第二次遍历, 得到skipRule的信息, 对抽象规则做记录
    for k,r in prot.abs_rule_map.items():
        if isinstance(r,murphi.MurphiRule):
            if r.name in abs2ori:
                rule_name = abs2ori[r.name]
            else:
                rule_name = r.name.replace('ABS_', '')
            not_skip.append(rule_name)
            param = list(rule_dict[rule_name]['limits'].keys())
            if len(param) == 1:
                # cond_res = {param[0]: False}
                cond_res = {'i': False}
            elif len(param) == 2:
                cond_res = {param[0]: False, param[1]: False}
            rule_dict[rule_name]["abstract"].append({"cond": cond_res,"answer": r.name})

        elif isinstance(r,murphi.MurphiRuleSet):
            rule_name = abs2ori[r.rule.name]
            decl = r.rule.name.split('_')[-1]
            param = list(rule_dict[rule_name]['limits'].keys())
            not_skip.append(rule_name)
            if len(r.var_decls)==1:
                if len(param) == 2:
                    cond_res = copy.deepcopy(rule_dict[rule_name]["abstract"][0]["cond"])
                    cond_res.update({decl:False})
                    rule_dict[rule_name]["abstract"].append({"cond": cond_res,"answer":r.rule.name})
                else:
                    raise ValueError("len of param must be 2")

            elif len(r.var_decls)==2:
                continue
        else:
             continue

    # print('not skip is {}'.format(not_skip))

    #第三次遍历,加入skipRule的信息
    for k,r in prot.ori_rule_map.items():    
        if isinstance(r,murphi.MurphiRuleSet):
            rule_name = r.rule.name.replace('_ref','')
            if rule_name not in not_skip:
                param = list(rule_dict[rule_name]['limits'].keys())
                if len(param) == 1:
                    # cond_res = {param[0]: False}
                    cond_res = {'i': False}
                    rule_dict[rule_name]["abstract"].append({"cond": cond_res,"answer": "skipRule"})
                elif len(param) == 2:
                    rule_dict[rule_name]["abstract"].append({"cond": {param[0]: False, param[1]:True},"answer": "skipRule"})
                    rule_dict[rule_name]["abstract"].append({"cond": {param[0]: True, param[1]:False},"answer": "skipRule"})
                    rule_dict[rule_name]["abstract"].append({"cond": {param[0]: False, param[1]:False},"answer": "skipRule"})
    
    return enum_type, rule_dict

def inv_2forall(filename):
    print("Reading file \"{}\"".format(filename)) 
    prot = parser.parse_file(filename)
    for name, inv in prot.lemma_map.items():
        cnt = 0
        tmp_expr = inv.inv
        while isinstance(tmp_expr, murphi.ForallExpr):
            para_typ = tmp_expr.typ
            tmp_expr = tmp_expr.expr
            cnt += 1
        #只有一层forall,需要再加一层
        if cnt == 1:
            temp_inv = murphi.MurphiInvariant(name, murphi.ForallExpr(murphi.MurphiVarDecl('m', para_typ), inv.inv))
            prot.decls.remove(prot.inv_map[name])
            prot.decls.append(temp_inv)
        else:
            prot.decls.remove(prot.inv_map[name])
            prot.decls.append(inv)
    with open(filename, 'w') as f:
        f.write(str(prot))

if __name__ == "__main__":
    data_dir = '.'
    protocol_name = 'flash_ctc10'
    #规范协议形式
    inv_2forall(filename='./{0}/ABS{0}.m'.format(protocol_name))
    #将ABS_ref中的未抽象规则全加上ref
    trans_ref(data_dir, protocol_name)
    #获取抽象过程
    # csv_f = open('{}/{}/abs_process.csv'.format(data_dir, protocol_name), 'r')
    # reader = csv.reader(csv_f)
    # abs_result = dict()
    # for line in reader:
    #     abs_result[line[0]] = line[1:]

    #生成json信息
    filename = '{0}/{1}/ABS_ref_{1}.m'.format(data_dir, protocol_name)
    enum_type, rule_dict = json_str_gen(filename = filename)
    # info_dict = json_gen(filename='ABS{}.m'.format(protocol_name),rule_dict = rule_dict, abs_result=abs_result)
    #加上加强的inv
    data = []
    data.append(enum_type)
    for k,v in rule_dict.items():
        data.append(v)
    for d in data:
        if 'ruleset' in d:
            # if d['ruleset'] in abs_result:
            #     d['strengthen'] = list(reversed(abs_result[d['ruleset']]))
            del d['limits']
    with open('{}_str.json'.format(protocol_name), 'w') as f:
        json.dump(data, f, indent=4)