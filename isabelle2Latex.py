import sys
import re
def isbelle2Latex(filename):
    maps=dict()
    digit='[0-9]'
    letter='[a-zA-Z]'
    letterdigit='[0-9a-zA-Z]'
    id=letter+'+(_'+letterdigit+"*)*"
    temp='(<'+id+'>)'
    rep='\\'+id
    temp1='[<>]'
    with open(filename,'r') as f:
        txt=f.read()
    regex=re.compile(temp)
    m=regex.findall(txt)
    print(m)
    for i,j in m:
        print(i)
        rep=re.sub(temp1,'',i)
        maps[i]=rep
    print('maps=')
    print(maps)
    maps['<or>']='lor'
    maps['<and>']='land'
    
    for k,r in maps.items():
        print("\\\\%s" % k)
        print('$\\\\%s$' % r)
        txt=re.sub("\\\\%s" % k, '$\\\\%s$' % r,txt)

    with open('%s_w.thy'%filename,'w') as f:
        f.write(txt)

if __name__ == '__main__':
    args=sys.argv
    if (args.__len__()==2):
        print(args[1])
        isbelle2Latex(args[1])
    else:
        pass