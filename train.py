import json


f=open("myproblems.txt",'r')


s=f.read()

f.close()


gir=json.loads(s)


print(gir[0]['size'])


gir.sort(key=lambda x:x['size'])

#for i in range(100):
#    print(gir[i])



####
# My magic parser
#
##

from pyparsing import nestedExpr


def evaluateBV(s):
    l=nestedExpr('(',')').parseString(s).asList()

    print(l)

    e=nlToS(l)
    return e


def nlToS(nl):
    if isinstance(nl,str):
        return nl
    if not isinstance(nl[0],str):
        assert len(nl)==1
        return "("+nlToS(nl[0])+")"
    elif nl[0]=="lambda":
        assert len(nl)==3
        return "( lambda "+nl[1][0]+" : "+nlToS(nl[2] )+")"
    elif nl[0]=="fold":
        assert len(nl)==4
        return "foldit("+\
            nlToS(nl[1])+","+\
            nlToS(nl[2])+","+\
            nlToS(nl[3][1][0])+","+\
            nlToS(nl[3][1][1])+","+\
            nlToS(nl[3][2])+\
            ")"
    elif nl[0]=="0" :
        assert len(nl)==1
        return " 0 "
    elif nl[0]=="1":
        assert len(nl)==1
        return " 1 "
    elif nl[0]=="if0":
        assert len(nl)==4
        return "( "+nlToS(nl[2]) + " if "+nlToS(nl[1])+" else "+nlToS(nl[3])+")"
    elif nl[0]=="not":
        assert len(nl)==2
        return "( 0xffffffffffffffffffffffffffffffff ^ "+nlToS(nl[1])+")"
    elif nl[0]=="shl1":
        assert len(nl)==2
        return "(( "+nlToS(nl[1])+"<<1)%(1<<64))"
    elif nl[0]=="shr1":
        assert len(nl)==2
        return "( "+nlToS(nl[1])+">>1)"
    elif nl[0]=="shr4":
        assert len(nl)==2
        return "( "+nlToS(nl[1])+">>4)"
    elif nl[0]=="shr16":
        assert len(nl)==2
        return "( "+nlToS(nl[1])+">>16)"
    elif nl[0]=="and":
        assert len(nl)==3
        return "( "+nlToS(nl[1])+" & "+nlToS(nl[2])+")"
    elif nl[0]=="or":
        assert len(nl)==3
        return "( "+nlToS(nl[1])+" | "+nlToS(nl[2])+")"
    elif nl[0]=="xor":
        assert len(nl)==3
        return "( "+nlToS(nl[1])+" ^ "+nlToS(nl[2])+")"
    elif nl[0]=="plus":
        assert len(nl)==3
        return "(("+nlToS(nl[1])+" + "+nlToS(nl[2])+")%(1<<64))"
    else:
        print("About to fail: "+nl)
        assert False
    

import urllib.request

trainURL="http://icfpc2013.cloudapp.net/train?auth=03322ZfXM9y7bAmubitseHsbGtSyUBS8Uqvv9YmBvpsH1H"
#trainURL="http://icfpc2013.cloudapp.net/path?train=0000abcdefghijklmnopqrstuvwxyz0123456789vpsH1H"
#details = urllib.parse.urlencode({})
details=json.dumps({'size':'3'})
details = details.encode('UTF-8')

f = urllib.request.urlopen(trainURL,details)
train=f.read().decode("utf-8")

s=json.loads(train)['challenge']

print(train)
print(s)
e=evaluateBV(s)

print("ee => ",e)
f=eval(e)


















