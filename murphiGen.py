import os
import argparse
import csv
from abstract import initAbs, test_abs_str

arg_parser = argparse.ArgumentParser(description='auto-CMP')
arg_parser.add_argument('--task', default='mutualEx')
args = arg_parser.parse_args()

data_dir = '.'
protocol_name = args.task

# Delete the old abstract protocol
if os.path.exists('./{0}/ABS{0}.m'.format(protocol_name)):
    os.remove('./{0}/ABS{0}.m'.format(protocol_name))

# Generate the new abstract protocol
initAbs("./{0}/{0}.m".format(protocol_name), "./ABS{0}.m".format(protocol_name))


abs_result = dict()    
csv_f = open('{}/{}/abs_process.csv'.format(data_dir, protocol_name))
reader = csv.reader(csv_f)
lemmas = set()
for line in reader:
    lemmas |= set(line[1:])
    abs_result[line[0]] = line[1:]
invs = []
for lemma in lemmas:
    with open('{}/{}/useful_rule/{}.txt'.format(data_dir, protocol_name, lemma), 'r') as f:
        inv = f.read()
        invs.append(inv)
# print(invs)
with open("./ABS{0}.m".format(protocol_name), 'a') as  f:
    for i in invs:
        f.write(i)
        f.write('\n')
csv_f.close()
for flag, ls in abs_result.items():
    test_abs_str(flag, name=protocol_name, lemmas=ls)

os.rename('{0}/ABS{1}.m'.format(data_dir, protocol_name), '{0}/{1}/ABS{1}.m'.format(data_dir, protocol_name))
