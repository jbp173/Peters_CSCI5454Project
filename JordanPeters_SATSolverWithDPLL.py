#Default: -1 == not present
#0 == False
#1 == True
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
    def setVars(self, newVars):
        self.vars = newVars
    #Gets the number of remaining variables that haven't been checked. Pures can be excluded from this count.
    def remainingVars(self, var, pures={}):
        count = 0
        for x in range(var,len(self.vars)):
            if self.vars[x] != -1 and x not in pures.keys():
                count = count + 1
        return count
    def solveRemaining(self, pures={}):
        #We go backwords, since we solve for variables forwards. If there's only one variable left, it'll be the latest remaining (that isn't pure). 
        for x in range(len(self.vars)-1, -1, -1):
            if self.vars[x] != -1 and x not in pures.keys():
                if self.vars[x] == 0:
                    return x, True
                else:
                    return x, False
        return -1

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

#Outputs the answer as a CNF format of a SAT problem in plain text
def toStringSolved(SATArray, solved):
    toPrint = ""
    for sat in range(0,len(SATArray)):
        toPrint = toPrint + "("
        varArray = SATArray[sat].getVars()
        for x in range(0,len(varArray)):
            if varArray[x] != -1:
                if varArray[x] == 1:
                    toPrint = toPrint + str(not solved[x])
                elif varArray[x] == 0:
                    toPrint = toPrint + str(solved[x])
                toPrint = toPrint + "||"
        toPrint = toPrint[:len(toPrint)-2]
        toPrint = toPrint + ")"
        if sat != len(SATArray)-1:
            toPrint = toPrint + "&&"
    print(toPrint)


#Remove any "pure" variables. A variable is "pure" if every occurence of it is either always not negated or always negated.
def findPures(SATArray, pures = {}):
    pureArray = {}   
    for i in range (0,len(SATArray[0].getVars())):
        #Start at blank value, set it to something when we find something
        polarity = -1
        first = True
        pure = True
        for j in range (0,len(SATArray)):
            #If the polarity of this clause at this variable isn't the same as the previous AND it isn't the blank code AND it isn't a variable we should be looking at
            if SATArray[j].getVars()[i] != polarity and SATArray[j].getVars()[i] != -1 and i not in pures.keys():
                #We found a non blank value for our variable
                if first == True:
                    first = False
                    polarity = SATArray[j].getVars()[i]
                #We found a different value, so it can't be pure
                else:
                    pure = False
                    break
        if pure == True:
            if (polarity == 0):
                pureArray[i] = True
            elif (polarity == 1):
                pureArray[i] = False
    return pureArray

#The function that does the actual work
#The answer that pops out of this is inversed, to make calcuations easier
total = []
def fun(bools, ar, pures, it=-1):
    #Base case: everything is satified, we're done!
    if len(ar) == 0:
        total.append("1")
        return (bools)
    #Base case: we've run out of variables, we can't satisfy with this config
    if it == len(bools):
        total.append("1")
        return False
    
    #Base case: there's a clause that's empty, which mean we can't satisfy 
    for x in ar:
        if x.remainingVars(it, pures) == 0:
            total.append("1")
            return False
    
    #The first iteration we just need to divide and recurse, since we don't actually have anything pluged in yet.
    if it != -1:        
        ar = removeTrue(bools[it], ar, it)
    #If a variable is pure, we already know what it has to be set to
    if it+1 in pures.keys():
        bools[it+1] = pures[it+1]
        return fun(list(bools),ar,pures,it+1)
    #Otherwise recurse and divide, test the next variable to look at with True and False to see if one satisfies
    else:
        test = fun(list(bools),ar,pures,it+1)
        if test != False:
            return test
        if it != len(bools) - 1:
            bools[it+1] = False
            return fun(list(bools),ar,pures,it+1)
        else:
            return False
        
#Helper function to remove statesments from the SATArray that have evaluated to True, so we don't need to do anything with them anymore. 
def removeTrue(boolean, ar, var):
    #How many SAT clauses are true.
    truths = []
    #Before we've checked any, we assume none are True
    for x in range(0,len(ar)):
        truths.append(False)
    #We now evaluate each caluse with our current variable we're looking at
    for x in range(0, len(ar)):
        truths[x] = ar[x].evalu(boolean,var)
    #Remove the SAT clauses that we've now satisfied
    for x in range(len(truths)-1,-1,-1):
        if truths[x] == True:
            ar = ar[:x] + ar[x+1:]
    return ar

#Get SAT representation array from input
file = open('CNF.txt')
SATArray, clauses, numVars = readInput(file)


#Do preprocessing until nothing changes (ie. there's nothing left to do)
pures = {}

#Comment out this line to effectively disable DPLL
pures = findPures(SATArray)



oldLength = len(pures.keys())
newLength = 0
while oldLength != newLength:
    
    oldLength = len(pures.keys())
    
    #Process out literals (clauses containing only one variable)
    #Python doens't like it when you itterate though something that you add to during itteration
    newPures = dict(pures)
    for x in pures.keys():
        SATArray = removeTrue(newPures[x], SATArray, x)
        for clause in SATArray:
            if clause.remainingVars(0, newPures) == 1:
                pos, boolean = clause.solveRemaining(newPures)
                #We're going to add it to our pures becuase it's a ground truth, which is essentially the same
                newPures[pos] = boolean
                SATArray = removeTrue(newPures[x], SATArray, x)
    pures = newPures
    
    #Process out pures, now with updated info
    pures = findPures(SATArray, dict(pures))
    
    newLength = len(pures.keys())


bools = []
for x in range(0,numVars):
    bools.append(True)


#Optional: print the SAT problem in plain text
#toString(SATArray)


#[True,False,True,False,True,True,True,True,True,False,True,True,True,False,False,True] should be the answer
#Actually run the thing, print the satifiablity array if there is one, otherwise print 'False'       
print("Running...")
out = (fun(bools, SATArray, pures))

#toStringSolved(SATArray, out)
print(out)

print("Operations:", len(total))
print("Finished.")



