import os
import argparse
import csv

from murphiparser import invariant_parser, parse_file
from abstract import strengthen, absTransfRule
import murphi

arg_parser = argparse.ArgumentParser(description='auto-CMP')
arg_parser.add_argument('--task', default='mutualEx')
args = arg_parser.parse_args()

data_dir = '.'
protocol_name = args.task

prot = parse_file('{}/{}/{}.m'.format(data_dir, protocol_name, protocol_name))


# Delete the old abstract protocol
if os.path.exists('./{0}/ABS{0}.m'.format(protocol_name)):
    os.remove('./{0}/ABS{0}.m'.format(protocol_name))

# Read abs_process file
abs_result = dict()    
with open('{}/{}/abs_process.csv'.format(data_dir, protocol_name)) as csv_f:
    reader = csv.reader(csv_f)
    lemmas = set()
    for line in reader:
        lemmas |= set(line[1:])
        abs_result[line[0]] = line[1:]

# Read invariants
invs = dict()
for lemma in lemmas:
    with open('{}/{}/useful_rule/{}.txt'.format(data_dir, protocol_name, lemma), 'r') as f:
        invs[lemma] = invariant_parser.parse(f.read())
        invs[lemma] = invs[lemma].elaborate(prot, dict())

for lemma in lemmas:
    prot.add_lemma(invs[lemma])

new_rules = list()
for rule_name in prot.rule_map:
    if isinstance(prot.rule_map[rule_name], murphi.MurphiRule):
        rule = prot.rule_map[rule_name]
        if rule_name in abs_result:
            for lemma_name in abs_result[rule_name]:
                rule = strengthen(rule, prot.lemma_map[lemma_name].inv)
        abs_rule = absTransfRule(rule, dict())
        if abs_rule and (rule.cond != abs_rule.cond or rule.cmds != abs_rule.cmds):
            new_rules.append(abs_rule)
    elif isinstance(prot.rule_map[rule_name], murphi.MurphiRuleSet):
        rule_set = prot.rule_map[rule_name]
        rule = rule_set.rule
        if rule_name in abs_result:
            for lemma_name in abs_result[rule_name]:
                rule = strengthen(rule, prot.lemma_map[lemma_name].inv)
        vars = tuple(rule_set.var_map.keys())
        if len(vars) == 1:
            abs_rule = absTransfRule(rule, {vars[0]: False})
            if abs_rule:
                new_rules.append(abs_rule)
        elif len(vars) == 2:
            abs_rule1 = absTransfRule(rule, {vars[0]: False, vars[1]: True}, "_" + vars[0])
            if abs_rule1:
                new_rules.append(murphi.MurphiRuleSet([murphi.MurphiTypeDecl(vars[1], rule_set.var_map[vars[1]])], abs_rule1))

            abs_rule2 = absTransfRule(rule, {vars[0]: True, vars[1]: False}, "_" + vars[1])
            if abs_rule2:
                new_rules.append(murphi.MurphiRuleSet([murphi.MurphiTypeDecl(vars[0], rule_set.var_map[vars[0]])], abs_rule2))

            abs_rule3 = absTransfRule(rule, {vars[0]: False, vars[1]: False}, "_" + vars[0] + "_" + vars[1])
            if abs_rule3:
                new_rules.append(abs_rule3)

for new_rule in new_rules:
    prot.add_abs_rule(new_rule)

with open("./ABS{0}.m".format(protocol_name), 'a') as f:
    f.write(str(prot))

os.rename('{0}/ABS{1}.m'.format(data_dir, protocol_name),
          '{0}/{1}/ABS{1}.m'.format(data_dir, protocol_name))
