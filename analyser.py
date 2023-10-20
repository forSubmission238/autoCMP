import re

def inv_strengthen(used_string_list, rule):
    str_global = []
    str_local = []
    for i, r in enumerate(used_string_list):
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
