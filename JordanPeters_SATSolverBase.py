#Default == 0 (false)
# -1 == not present
# 1 == true
class SAT(object):
    def __init__(self, array):
        self.vars = array
    def evalu(self,test,var):
        #Variable isn't present, so this clause has to be tested furthur.
        if self.vars[var] == -1:
            return False
        #If variable is present, evaluate it to see if we've satisfied it or need to keep working to satify it.
        return (self.vars[var] ^ test)
    def getVars(self):
        return self.vars   

#Generate an array of SAT object corresponding to DIMACS CNF format for SAT
def readInput(file):
    SATArray = []
    basicVars = []
    updatedVars = []
    clauses = 0
    numVars = 0
    for line in file:
        split = line.split()
        if split[0] == "c":
            continue
        elif split[0] == "p":
            numVars = int(split[2])
            for i in range(0,numVars):
                basicVars.append(-1)
            clauses = int(split[3])
            clausesCopy = clauses
            updatedVars = list(basicVars) #need a deep copy
        else:
            for x in split:
                if x == "0":
                    SATArray.append(SAT(updatedVars))
                    updatedVars = list(basicVars)
                    clausesCopy = clausesCopy - 1
                else:
                    negation = 1
                    if x[0] == "-":
                        negation = 0
                        x = x[1:]
                    updatedVars[int(x)-1] = negation #DIAMACS indexes from 1, because ugh
    
    #Last clause doesn't have to end with 0, because why not, so we have to check for that
    if clausesCopy > 0:
        SATArray.append(SAT(updatedVars))

    return SATArray, clauses, numVars

#Outputs CNF format of a SAT problem in plain text
def toString(SATArray):
    toPrint = ""
    for sat in range(0,len(SATArray)):
        toPrint = toPrint + "("
        varArray = SATArray[sat].getVars()
        for x in range(0,len(varArray)):
            if varArray[x] != -1:
                if varArray[x] == 1:
                    toPrint = toPrint + str(x+1)
                elif varArray[x] == 0:
                    toPrint = toPrint + "-" + str(x+1)
                toPrint = toPrint + "||"
        toPrint = toPrint[:len(toPrint)-2]
        toPrint = toPrint + ")"
        if sat != len(SATArray)-1:
            toPrint = toPrint + "&&"
    print(toPrint)
    
    
total = []
def fun(bools, ar, it=-1):
    #Base case: everything is satified, we're done!
    if len(ar) == 0:
        total.append("1")
        return (bools)
    #Base case: we've run out of variables, we can't satisfy with this config
    if it == len(bools):
        total.append("1")
        return False
    
    #Initial iteration split
    if it == -1:
        test = fun(list(bools),ar,0)
        if test != False:
            return test
        bools[0] = False
        return fun(list(bools),ar,0)   
    else:        
        #How many SAT clauses are true.
        truths = []
        #Before we've checked any, we assume none are True
        for x in range(0,len(ar)):
            truths.append(False)
        #We now evaluate each caluse with our current variable we're looking at
        for x in range(0, len(ar)):
            truths[x] = ar[x].evalu(bools[it],it)
        #Remove the SAT clauses that we've now satisfied
        for x in range(len(truths)-1,-1,-1):
            if truths[x] == True:
                ar = ar[:x] + ar[x+1:]
        #Recurse and divide, test the next variable to look at with True and False to see if one satisfies
        test = fun(list(bools),ar,it+1)
        if test != False:
            return test
        if it != len(bools) - 1:
            bools[it+1] = False
            return fun(list(bools),ar,it+1)
        else:
            return False
      
        
        
#Get SAT representation array from input
file = open('CNF.txt')
SATArray, clauses, numVars = readInput(file)
bools = []
for x in range(0,numVars):
    bools.append(True)
    
#Optional: print the SAT problem in plain text
#toString(SATArray)

#[True,False,True,False,True,True,True,True,True,False,True,True,True,False,False,True] should be the answer
#Actually run the thing, print the satifiablity array if there is one, otherwise print 'False'       
print("Running...")
print(fun(bools, SATArray))
print("Operations:", len(total))
print("Finished.")



