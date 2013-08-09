import json
from random import randint
from pyparsing import nestedExpr
from functools import reduce
import urllib.request

def doPrintMyProblems():

    f=open("myproblems.txt",'r')


    s=f.read()

    f.close()


    gir=json.loads(s)


    print(gir[0]['size'])


    gir.sort(key=lambda x:x['size'])

    for i in range(100):
        print(gir[i])



####
# My magic parser
#
##




def evaluateBV(s):
    l=nestedExpr('(',')').parseString(s).asList()

    #print(l)

    e=nlToS(l)
    return e



def foldit(e0,e1,x,y,e2):
        return "reduce( lambda "+y+","+x+":"+e2+", ["+e1+\
               "] + [( z>>(i*8))%(1<<8) for z in ["+\
               e0+"] for i in range(8) ])"


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
        return foldit(
            nlToS(nl[1]),
            nlToS(nl[2]),
            nl[3][1][0],
            nl[3][1][1],
            nlToS(nl[3][2]),
            )
    elif nl[0]=="0" :
        assert len(nl)==1
        return " 0 "
    elif nl[0]=="1":
        assert len(nl)==1
        return " 1 "
    elif nl[0]=="if0":
        assert len(nl)==4
        return "( "+nlToS(nl[2]) + " if "+nlToS(nl[1])+"==0 else "+nlToS(nl[3])+")"
    elif nl[0]=="not":
        assert len(nl)==2
        return "( ((1<<64)-1) ^ "+nlToS(nl[1])+")"
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
    


####
# Make sure the parser is working
#
#####





def doCheckParser():

    trainURL="http://icfpc2013.cloudapp.net/train?auth=03322ZfXM9y7bAmubitseHsbGtSyUBS8Uqvv9YmBvpsH1H"
    #trainURL="http://icfpc2013.cloudapp.net/path?train=0000abcdefghijklmnopqrstuvwxyz0123456789vpsH1H"
    #details = urllib.parse.urlencode({})
    details=json.dumps({'size':29,'operators':["tfold"]})
    details = details.encode('UTF-8')

    f = urllib.request.urlopen(trainURL,details)
    train=f.read().decode("utf-8")

    bvChallenge=json.loads(train)['challenge']

    print("\nGot challenge program:\n",bvChallenge)

    #print(train)
    #print(bvChallenge)
    e=evaluateBV(bvChallenge)

    print("\nee => ",e)
    bvFunction=eval(e)

    
    testVectors=[randint(0,(1<<64)-1) for i in range(10)]


    evalRequest=json.dumps({
        "program":bvChallenge,
        "arguments":["0x%016X"%x for x in testVectors]
        })

    print("\nEvalRequest:\n",evalRequest)
    evalRequestB = evalRequest.encode('UTF-8')

    testURL="http://icfpc2013.cloudapp.net/eval?auth=03322ZfXM9y7bAmubitseHsbGtSyUBS8Uqvv9YmBvpsH1H"

    f = urllib.request.urlopen(testURL,evalRequestB)
    test=f.read().decode("utf-8")


    bvTest=json.loads(test)

    print(bvTest)


    bvGuess=["0x%016X"%bvFunction(x) for x in testVectors]

    for (x,y) in zip(bvTest['outputs'],bvGuess):
        gir="" if x==y else "!!!"
        print(x,y,gir)





#####
#
# Try exhaustively generating all programs
#
#####

def getPartitions(n,k):
    if k==1:
        return [ [n] ]
    out=[]
    for i in range(1,n):
        pp=getPartitions(n-i,k-1)
        #print("about to die",i,pp)
        out+=[ [i]+x for x in pp  ]
    return out


#return all programs of a given size with the specified operators
def generateAllPrograms(ops,size):
    if "tfold" in ops:
        opss=list(ops)
        opss.remove("tfold")
        vl0=["x"]
        vl1=["y","z"]
        #split size among e0,e1,e1
        out=[]
        print("gir",getPartitions(size-3,3))
        print("girr",opss)
        
        for p0,p1,p2 in getPartitions(size-3,3):
            e0l=gv(vl0,opss,p0)
            e1l=gv(vl0,opss,p1)
            e2l=gv(vl1,opss,p2)
            
            out+=[ "(lambda (x) (fold "+x+" "+y+\
                   "(lambda (y z) "+z+")))"
                   for x in e0l
                   for y in e1l
                   for z in e2l]
        return out
               
    else:
        vl=["x"]
        e0l=gv(vl,ops,size-1)
        print("got here",len(e0l),ops,vl,size-1)
        return ["(lambda (x) "+x+")" for x in e0l]


#given a set of operators, variables and a size
# return a list of all valid expressions
op1=["not" , "shl1" , "shr1" , "shr4" , "shr16"]
op2=["and" , "or" , "xor" , "plus" ]


def gv(vl,ops,size):
    if size==1:
        return [ x for x in vl+["0","1"] ]
    out=[]
    for op in ops:
        if op=="fold" and size>=5:
            opss=list(ops)
            opss.remove("fold")
            vl1=["y","z"]
            for p0,p1,p2 in getPartitions(size-2,3):
                e0=gv(vl,opss,p0)
                e1=gv(vl,opss,p1)
                e2=gv(vl1,opss,p2)
                out+=["fold "+x+" "+y+\
                      +" (lambda (y z) "+z+"))"
                      for x in e0
                      for y in e1
                      for z in e2]
        elif op=="if0" and size>=4:
            for p0,p1,p2 in getPartitions(size-1,3):
                e0=gv(vl,ops,p0)
                e1=gv(vl,ops,p1)
                e2=gv(vl,ops,p2)
                out+=["(if0 "+x+" "+y+\
                      " "+z+")"
                      for x in e0
                      for y in e1
                      for z in e2]
                
        elif op in op1 and size>=2:
            e0=gv(vl,ops,size-1)
            out+=["("+op+" "+x+")"
                  for x in e0 ]
        elif op in op2 and size>=3:
            for p0,p1 in getPartitions(size-1,2):
                e0=gv(vl,ops,p0)
                e1=gv(vl,ops,p1)
                out+=["("+op+" "+x+" "+y+")"
                      for x in e0
                      for y in e1]
        else:
            #print("This should never happen!",op,size)
            #assert False
            pass
    return out



def doTestGenP(size=5):

    trainURL="http://icfpc2013.cloudapp.net/train?auth=03322ZfXM9y7bAmubitseHsbGtSyUBS8Uqvv9YmBvpsH1H"
    #trainURL="http://icfpc2013.cloudapp.net/path?train=0000abcdefghijklmnopqrstuvwxyz0123456789vpsH1H"
    #details = urllib.parse.urlencode({})
    details=json.dumps({'size':size,'operators':["tfold"]})
    details = details.encode('UTF-8')

    f = urllib.request.urlopen(trainURL,details)
    train=f.read().decode("utf-8")

    bvChallenge=json.loads(train)

    print(bvChallenge)

    ops=bvChallenge['operators']
    size=bvChallenge['size']

    allPrograms=generateAllPrograms(ops,size)

    #for i,p in enumerate(allPrograms):
    #    print(i,"=>\n",p)

    #print("program in list:",bvChallenge['challenge'] in allPrograms)
    #need a better way to check if program is in list

    print("num programs: ",len(allPrograms) )


if __name__=="__main__":
    doTestGenP(8)













    







