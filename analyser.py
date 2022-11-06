import re

class TypeDef(object):
    """
    Deal with type and const in murphi

    It can deal with the following definition:
        const
            NODE_NUM : 3;
            DATA_NUM : 2;
        type
            NODE : scalarset(NODE_NUM);
            DATA : 1..DATA_NUM;

    and turn it into:
        self.type = {NODE:NODE_NUM, DATA: DATA_NUM}
        self.const = {NODE_NUM : 3, DATA_NUM:2}
        para = ["NODE"] -- because the type used to represent 'processor' is usually used with 'array [__] of'
    """

    def __init__(self, text):
        self.text = text
        self.type = {}
        self.const = {}
        self.para = []
        self.enumvalues = set()
        self.evaluate()

    def evaluate(self):
        self.eval_scalarset()
        self.eval_const()
        self.eval_arr()
        self.evalEnum()
        # print(self.type, self.const, self.para, self.enumvalues)

    def evalEnum(self):
        enums = re.findall(r'(\w*?)\s*:\s*enum\s*\{(.*?)\}\s*;', self.text, re.S)
        for _, vstr in enums:
            values = list(filter(lambda x: x, list(map(lambda y: y.strip(), vstr.split(','))))) #['I', 'T', 'C', 'E']
            for v in values:
                self.enumvalues.add(v)

    def eval_scalarset(self):
        """
        collect types from two kinds of type:
            1. NODE: 1..NODE_NUM
            2. NODE: scalarset(NODE_NUM)

        :param text: murphi description
        :return: NONE
        """
        scalarsets = re.findall(r'(\w*?)\s*:\s*\w+?\s*\.\.\s*(\w+?)\s*;', self.text, re.S)
        scalarsets2 = re.findall(r'(\w*?)\s*:\s*scalarset\((\w+)\)', self.text, re.S)

        self.type.update({name: num for name, num in scalarsets}) 
        self.type.update({name: num for name, num in scalarsets2}) #{'NODE': 'NODENUMS'}

    def eval_arr(self):
        """
        For now, the type that will be used as a represent of a processor usually can be found in form of :
        array [NODE] of ...
        So identifying it using 'array [\w+] of', and check whether it is in self.types.
        :return:
        """
        pattern = re.compile(r'array\s*\[\s?(\w+)\s?\]\s*of\s*.+')
        array = list(set(re.findall(pattern, self.text))) 
        self.para = [a for a in array if a in self.type] #['NODE']

    def eval_const(self):
        config = re.findall(r'(\w+)\s*:\s*(\d+)\s*;', self.text)
        self.const = {v: d for v, d in config}

    def reset_const(self, para, num):
        """
        reset the configuration by the given parameter name and new number
        :param para:
        :param num:
        :return: new murphi description
        """
        para_const = self.type[para]
        self.text = re.sub(r'%s\s?:\s?(\d+?)\s?;' % para_const, r"%s : %d;" % (para_const, num), self.text)
        return self.text


class Field(object):
    def __init__(self):
        self.para_dict = {}
        self.content = []

def pair_2_dict(key_dict, value_dict):
    # assert len(key_dict) == len(value_dict)
    new_dict = {}
    # for k, v in zip(key_dict.values(), value_dict.values()):
    for k in value_dict.keys():
        new_dict[key_dict[k]] = value_dict[k]
    return new_dict


def norm_rep(rep_dict, lst):
    norm_lst = []
    for item in lst:
        for p, t in rep_dict.items():
            item = re.sub(r'\b%s\b' % p, t, item)
        norm_lst.append(item)
    return norm_lst

def number_type(origin_dict):
    new_dic, type_count, rev_dic = {}, {}, {}
    for p, t in origin_dict.items():
        if t not in type_count:
            type_count[t] = 1
        else:
            type_count[t] += 1
        new_dic[p] = '%s_%d' % (t, type_count[t])
        rev_dic['%s_%d' % (t, type_count[t])] = p
    return new_dic, rev_dic

class Guard(object):
    def __init__(self, text, param_name_dict):
        self.param_name_dict = param_name_dict
        self.text = text
        self.all_sentence = set()
        self.normal_guards = set()
        self.mainfield = Field()
        self.mainfield.para_dict = param_name_dict
        self.forfield = []
        self.existfield = []
        # self.sparse()

    def sparse(self):
        def para_repl(match):
            return self.param_name_dict[match.group()] if match.group() in self.param_name_dict else match.group()

        split_guard = list(map(lambda x: x.strip(), self.text.split('&')))
        for g in split_guard:
            if g.startswith(('forall', '!forall')):
                self.deal_forall(g)
            elif g.startswith(('exists', '!exists')):
                self.deal_exist(g)
            else:
                # self.guards.add(re.sub('\w+', para_repl, g))
                self.all_sentence.add(g)
                self.mainfield.content.append(g)

    def deal_forall(self, text):
        pattern = re.compile(r'forall(.*?)do(.*)end', re.S)
        try:
            params, content = re.findall(pattern, text)[0]
        except:
            print('cannot deal with %s ' % text)
        else:
            temp_field = Field()

            param_name_dict, _ = analyzeParams(params)
            temp_field.para_dict = param_name_dict
            # for var, type in param_name_dict.items():
            # parts = set(filter(lambda x: x, map(lambda x: re.sub('%s' % var, type, x.strip()),
            #                 filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content)))))
            parts = set(filter(lambda x: x, map(lambda x: x.strip(),
                                                filter(lambda x: len(x) > 2,
                                                       re.split(r'&', content)))))
            # re.split(r'(\||->|\n|\(|\)|&)', content)))))

            temp_field.content = list(filter(lambda x: x, map(lambda x: x.strip(),
                                                              filter(lambda x: len(x) > 2,
                                                                     re.split(r'&', content)))))
            # re.split(r'(\||->|\n|\(|\)|&)', content)))))
            self.all_sentence |= parts
            self.forfield.append(temp_field)

    def deal_exist(self, text):
        pattern = re.compile(r'!?exists(.*?)do(.*)end', re.S)
        try:
            params, content = re.findall(pattern, text)[0]
        except:
            print('cannot deal with %s ' % text)

        temp_field = Field()
        
        param_name_dict,_ = analyzeParams(params)
        temp_field.para_dict = param_name_dict
        #Python 字典(Dictionary) items() 函数以列表返回可遍历的(键, 值) 元组数组。
        '''
        tinydict = {'Google': 'www.google.com', 'Runoob': 'www.runoob.com', 'taobao': 'www.taobao.com'}
 
        print "字典值 : %s" %  tinydict.items()
 
        # 遍历字典列表
        for key,values in  tinydict.items():
        print (key,values)
        字典值 : [('Google', 'www.google.com'), ('taobao', 'www.taobao.com'), ('Runoob', 'www.runoob.com')]
        Google www.google.com
        taobao www.taobao.com
        Runoob www.runoob.com
        '''
        for var, type in param_name_dict.items(): 
            # for var, type, statesment in forall_parts:
            parts = set(map(lambda x: re.sub(var, type, x.strip()),
                            filter(lambda x: len(x) > 2,
                                   re.split(r'&', content))))  # re.split(r'(\||->|\n|\(|\)|&)', content))))
            temp_field.content = list(map(lambda x: x.strip(),
                                          filter(lambda x: len(x) > 2, re.split(r'&',
                                                                                content))))  # re.split(r'(\||->|\n|\(|\)|&)', content))))
            self.all_sentence |= parts
            self.existfield.append(temp_field)

    def evaluate(self):
        # print('guards here:%s' % self.all_sentence)
        print('\n[Guard part]')
        print('- main field: \n\t- parameters: %s\n\t- content:%s' % (self.mainfield.para_dict, self.mainfield.content))
        for item in self.forfield:
            print('- forfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))
        for item in self.existfield:
            print('- existfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))

    def collect_atoms(self):
        atoms = set()
        dic = self.mainfield.para_dict
        for item in self.forfield:
            dic.update(item.para_dict)
        for item in self.existfield:
            dic.update(item.para_dict)
        for guard in self.all_sentence:
            for k, v in dic.items():
                guard = re.sub(r'\b%s\b' % k, v, guard, re.I)
            atoms.add(guard)
        return atoms

def inv_strengthen(used_string_list, rule, all_types, NODE2para_dict):
    str_global = []
    str_local = []
    for i, r in enumerate(used_string_list):
        # murphi_string = to_murphi(inv_name='',rule=r, all_types=all_types,NODE2para_dict=NODE2para_dict)
        murphi_string = r
        content = re.findall(r'invariant.*?->\n(.*?);',murphi_string,flags=re.S)[0]
        if 'forall' in content:
            content = re.sub(r'\nend', '', content, flags=re.S)
            content += '\nend'
            str_local.append(content)
        else:
            content = re.sub(r'\nend', '', content)
            str_global.append(content)
    pre = rule.split('==>')[0]
    action = rule.split('==>')[1]
    str_info = pre
    for c in str_global:
        str_info += '& {}'.format(c)
    if len(str_local) != 0:
        str_info += '\n&'
        str_info += '&'.join(str_local)
    str_info += '\n==>\n'
    str_info += action
    return str_info

class Ruleset(object):
    def __init__(self, data_dir, protocol_name, text, type):
        self.data_dir = data_dir
        self.protocol_name = protocol_name
        self.text = text
        self.type = type
        self.guards = set()
        self.atoms = set()
        self.print_info = ""
        self.used_inv_string_set = set()
        self.dict_used_inv = {}

    def collect_atoms_from_ruleset(self):
        pattern = re.compile(r'ruleset(.*?)do(.*?)endruleset\s*;', re.S)
        rulesets = pattern.findall(self.text)
        for params, rules_str in rulesets:
            param_name_dict,_ = analyzeParams(params)
            rules = re.findall(r'(rule.*?endrule;)', rules_str, re.S)
            for each_rule in rules:
                self.collect_atoms_from_rule(each_rule, param_name_dict)

    def collect_atoms_from_rule(self, rule_text, param_name_dict):
        pattern = re.compile(r'rule\s*\"(.*?)\"\s*(.*?)==>.*?begin(.*?)endrule\s*;', re.S)
        rule_name, guards, _ = pattern.findall(rule_text)[0]
        guard_obj = Guard(guards, param_name_dict)
        guard_obj.sparse()
        # if guard_obj:
        self.atoms |= guard_obj.collect_atoms()
        # print('collect atoms from %s' % rule_name)

def analyzeParams(params):
    """
    @param params: as `i:Node; j:Node`
    @return a tuple as `{'i': 'Node', 'j': 'Node'}
    """
    if not params: return {}, '[]'
    parts = params.split(';')
    param_name_dict = {}
    para_name_list = []
    for p in parts: 
        param_name_dict[p.split(':')[0].strip()] = p.split(':')[1].strip()
        para_name_list.append(p.split(':')[0].strip())

    return param_name_dict, para_name_list


class Protocol(object):
    def __init__(self, data_dir, protocol_name, file_url, home): #data_dir = './protocols';file_url = '{0}/{1}/{1}.m'.format(data_dir, args.protocol)
        self.data_dir = data_dir
        self.protocol_name = protocol_name
        self.file_url = file_url
        self.home = home
        self.logfile = '{}/{}/prot.abs'.format(self.data_dir, self.protocol_name)

    def read_file(self):
        return open(self.file_url).read()

    def show_config(self):
        text = self.read_file()
        config = re.findall(r'(\w+)\s*:\s*(\d+)\s*;', text)
        for name, num in config:
            print('{} : {}'.format(name, num))

    def collect_atoms(self):
        text = self.read_file()
        typedf = TypeDef(text)
        # ruleset = Ruleset(self.data_dir, self.protocol_name, text, typedf.para)
        # ruleset.collect_atoms_from_ruleset()
        return typedf.type
