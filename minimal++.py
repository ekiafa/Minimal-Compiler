#############################################################
                        #Omada
            #Eftihia Kiafa AM 3003 cse53003
            #Kyrkenidis Anestis AM 3016 cse53016
#############################################################
#############################################################

# Minimal++ Compiler 

#To run the analysis do:
# python3 minimal++.py -i <file_name>


##############################################################

                        #Declarations 

###############################################################
import sys, getopt, enum, os, struct

lineNumber = -1 
charNumber = -1
end_of_file = 0
name = ""
showfile="" #global for the file read, in order to use in the lexicalAnalyzer()
nontoken="" #for id and numbers, basically anything not in the list below
tokens= ["+","-",'*',"/",",",":",";","<",">","<=",">=","=","<>",":=","(",")","{","}","[","]",
"program","declare","if","else","while","doublewhile","loop","exit","forcase","incase","when",
"default","not","and","or","function","procedure","call","return","in","inout","input","print","EOF"]
c_file = ""
int_file = ""
finalfile = ""
quadlist = []
nextquadlabel = 0
templist = [] #global list with the temp variables used
nexttemp = 0 #global integer zerved for the next temp ( used to differentiate the temporary variables) 
program_name = "" # needed for intermediate code
func = "" # needed for intermediate code
mainPFrameLength=-1
scopeList=[]
halt=-1 #halt label
subprogramExists = False #label for subrograms in final code
inFunctionBlock=[]  
haveReturn=[]
subprogramParams=[]
parameterC = "("

#class that acts as a struct for the Quads


class Quad():
    def __init__(self, label, op, x, y, z):
        self.label = label
        self.op = op
        self.x = x
        self.y = y
        self.z = z

    def writeQuadToFile(self):
        return str(self.label) +': ('+str(self.op)+', '+str(self.x)+', '+str(self.y)+', '+str(self.z)+')'



#class for Scope as a data pack for this element
class Scope():
    def __init__(self, enlevel=0,enclosing_scope=None):
        self.entities=[]
        self.enlevel = enlevel
        self.enclosing_scope= enclosing_scope
        self.toffset=12

        
    def addEntity(self,entity):
        self.entities.append(entity)
        
    def getOffset(self):
        returnValue=self.toffset
        self.toffset+=4
        return returnValue
        
#class for Entity as a data pack for this element
class Entity():
    def __init__(self,name,entityType):
        self.name=name
        self.entityType=entityType

#class for Fuction as a data pack for this element       
class Function(Entity):
    def __init__(self,name,returnType,startQuad=-1):
        super().__init__(name,'Function')
        self.returnType=returnType
        self.startQuad=startQuad
        self.arguments=[]
        self.framelength=-1
        
        
    def addArguments(self,argument):
        self.arguments.append(argument)
    
    def setFramelength(self,framelength):
        self.framelength=framelength
        
        
    def setStartQuad(self,startQuad):
        self.startQuad=startQuad
        
#class for Parameter as a data pack for this element
class Parameter(Entity):
    def __init__(self,name,parameterMode,offset=-1):
        self.parameterMode=parameterMode
        self.offset=offset
        super().__init__(name,'Parameter')


#class for Argument as a data pack for this element
class Argument():
    def __init__(self,parameterMode,nextArgument=None):
        self.parameterMode=parameterMode
        self.nextArgument=nextArgument
    
    def setNextArgument(self,nextArgument):
        self.nextArgument=nextArgument

class Variable(Entity):
    def __init__(self,name,offset=-1):
        super().__init__(name,'Variable')
        self.offset=offset
        

class TempVariable(Entity):
    def __init__(self,name,offset=-1):
        super().__init__(name, "TempVariable")
        self.offset=offset



#########################################################

                #Lexical Analyzer

#########################################################

def lexicalAnalyzer():
    global lineNumber,charNumber,char,showfile,nontoken, end_of_file
    buffer = [] 
    tokenLine = tokenChar= -1 
    commentLine = commentChar = -1 
    state = 0 
    finalState = -2
    foundChar = False 
    count=0
    
    #lexical analyzer automata 
    while state != finalState:
        char = showfile.read(1)
        buffer.append(char)
        charNumber += 1
        #print(str(charNumber))
        if state == 0:
            if char.isalpha():
                state = 1
            elif char.isdigit():
                state = 2
            elif char == '<':
                state = 3
            elif char == '>':
                state = 4
            elif char == ':':
                state = 5
            elif char == '/':
               state = 6
            elif char in ('+', '-', '*', '=', ',', ';', '{', '}', '(', ')', '[', ']'):
                state = finalState
            elif char == '': # EOF
                #print("REACHED END")
                end_of_file = 1
                return ("EOF")
                #sys.exit()
            elif char.isspace():
                state = 0
            else:
                ErrorFunc("Invalid char in program " + char +"'.")
        elif state == 1:
            if not char.isalnum():
                foundChar = True
                state = finalState
            #print(str(state))
        elif state == 2:
            if not char.isdigit():
                if char.isalpha():
                    ErrorFunc("Variables can't begin with numbers. Please start a variable with an alphabetic character.")
                foundChar = True
                state = finalState
        elif state == 3:
            if char != '=' and char != '>':
                foundChar = True
            state = finalState
        elif state == 4:
            if char != '=':
                foundChar = True
            state = finalState
        elif state == 5:
            if char != '=':
                foundChar = True
            state = finalState
        elif state == 6:
            if char == '*':
                state = 7
                commentLine = lineNumber
                commentChar = charNumber - 1
            elif char != "/" and char != "*":
                state = finalState
        elif state == 7:
            if char == '': # EOF
                ErrorFunc("Unclosed comment found.")
            elif char == '*':
                state = 8
        elif state == 8:
            if char == '/':
                del buffer[:]
                state = 0
            else:
                state = 7
        if state == finalState:
            tokenLine = lineNumber
            tokenChar = charNumber - len(''.join(buffer)) + 1
        if char.isspace():
            del buffer[-1]
            foundChar = False
            if char == '\n':
                lineNumber += 1
                charNumber = 0
    if foundChar == True:
        del buffer[-1]
        if char != '':#EOF
            showfile.seek(showfile.tell() -1)
        charNumber -=1
    nontoken = "empty"
    bufferContents= ''.join(buffer)
    if bufferContents not in tokens:
        if bufferContents.isdigit():
            nontoken="number"
            returnToken=bufferContents 
        else:
            nontoken="id"
            returnToken=bufferContents[:30] #cant be more than 30
    else:
            returnToken=bufferContents
    #print(bufferContents)
    del buffer [:]
    #print(str(state))
    #print(str(returnToken))
    return returnToken

def ErrorFunc(message):
    global lineNumber, charNumber
    print("======ERROR Detected!======")
    print(message + "(At line : " + str(lineNumber + 2) +")")
    showfile.close()
    sys.exit()



###################################################################

                    #Intermediate Code Functions

###################################################################

def nextquad(): # return the number of the next quad
    global nextquadlabel
    return nextquadlabel

def genquad(op=None, x='_', y='_', z='_'): # generate a new quad with the parameters given
    global nextquadlabel
    tmplabel = nextquadlabel
    nextquadlabel+=1
    temp = Quad(tmplabel, op, x, y, z)
    #print("XXXX ",x)
    quadlist.append(temp)

def newTemp(): # return the next Temp ( i.e T_1 ) to be used
    global templist, nexttemp
    key = "T_" + str(nexttemp)
    templist.append(key)
    scopeList[-1].addEntity(TempVariable(key, scopeList[-1].getOffset()))
    nexttemp+=1
    #print("Key : ",key)
    return key

def emptylist(): # create an empty quad list
    global quadlist
    quadlist.clear()

def makelist(x): # create an empty quad list that has only 'x' in it
    return [x]

def mergelist(l1, l2): # merge the 2 lists ( l1 and l2 )
    return l1 + l2

def backpatch(a1, z): # put in each quad of the list, the 'z' at the 4th element of each quad
    global quadlist
    for i in quadlist:
        if i.label in a1:
            i.z = z

####################### Utility Function #######################3

def is_number(n):
    try:
        int(n)   # Type-casting the string to `int`.
        # if the string is a number then it will return true
        # if not then it goes to exception
        return True
    except ValueError:
        return False



def findVariables(quad):
    vars=dict()
    index=quadlist.index(quad)+1
    while True:
        q=quadlist[index]
        if q.op=='end_block':
                break
        if (q.y !='CV' and q.y!='REF' and q.y!='RET') and q.op!= 'call'  and q.x!='':
                if isinstance(q.x, str):
                    if(is_number(q.x) == False ):
                        vars[q.x] = 'int'
                if isinstance(q.y, str):
                    if(is_number(q.y) == False ):
                        vars[q.y] = 'int'
                if isinstance(q.z, str):
                    vars[q.z] = 'int'
        index += 1
        if '_' in vars:
            del vars['_']
    return vars.items()


def transformToCdeclarations(vars):
    inVars= False
    returnValue='int '
    for var in vars:
        inVars= True
        returnValue+= var[0] + ', ' 
    if inVars==True:
        return returnValue[:-2]+';'
    else:
        return ''




def c_equivalent(quad):
    global parameterC
    
    haveSeenBlock=False
    returnCommand=""
    #reg Operators
    if quad.op in ('<=','>','>=','=','<>','<'):
        op= quad.op
        if op== '=':
           op='=='
        elif op == '<>':
           op='!='
        returnCommand= 'if ('+str(quad.x)+' '+op+' '+str(quad.y)+') goto Line_'+ str(quad.z)+';'
    #math operators
    elif quad.op in ('+','-','*','/'):
        returnCommand = quad.z +'='+str(quad.x)+' '+str(quad.op)+' '+str(quad.y)+';'
    #evaluation
    elif quad.op == ':=':
        returnCommand = quad.z + '=' + str(quad.x) + ';'
    #out
    elif quad.op == 'out':
       returnCommand = 'printf("%d\\n", '+str(quad.x)+');'
    elif quad.op == 'retv':
        returnCommand = 'return ('+str(quad.x)+');'
    #beginblock 
    elif quad.op == 'begin_block':
        haveSeenBlock = True
        if quad.x == program_name:
            returnCommand = 'int main(void)\n{\n'
        else:
            returnCommand = 'int '+ quad.x +'()\n{\n'
        vars = findVariables(quad)
        returnCommand += '   ' + transformToCdeclarations(vars) 
        returnCommand += '\nLine_'+str(quad.label) +':'
    #endblock
    elif quad.op == 'end_block':
        haveSeenBlock = True
        returnCommand = 'Line_'+str(quad.label)+': {}\n'
        returnCommand += '}\n'
    #halt
    elif quad.op == 'halt':
        returnCommand = 'return 0;'
    #jump
    elif quad.op=='jump':   
        returnCommand='goto Line_'+str(quad.z) + ';'

    elif quad.op == "par":
        if quad.y == "CV":
            parameterC+=" "+quad.x+","
        elif quad.y == "REF":
            parameterC+="&"+quad.x+","
        elif quad.y == "RET":
            print("par ", quad.x)
            parameterC=str(quad.x)+"="+parameterC+")"
    #call
    elif quad.op == 'call':
        tmp = 0
        for par in range(len(parameterC)):
          if parameterC[par]=="=":
            tmp=par
        parameterC=parameterC[0:tmp+1]+quad.x+parameterC[tmp+1:]+";"
        parameterC = parameterC.replace(',);', ' );')
        returnCommand = parameterC
    else:
        return None
    if haveSeenBlock== False:
        returnCommand = '   Line_' + str(quad.label) + ': ' + returnCommand
    return returnCommand

def makeIntermediateCodeFile():
    global quadlist
    for quad in quadlist:
        int_file.write(quad.writeQuadToFile() +'\n')
    int_file.close()  


def makeCcodeFile():
    global quadlist
    c_file.write('#include <stdio.h>\n\n')
    for quad in quadlist:
        #print("Whatever\n")
        a = c_equivalent(quad)
        if a is not None:
            c_file.write('' + a + '\n')
    c_file.close()




#############################################################

#               Symbol Table Functions

#############################################################




def addNewScope():
    enclosing_scope = scopeList[-1]
    currentScope= Scope(enclosing_scope.enlevel+1,enclosing_scope)
    scopeList.append(currentScope)


    
def addFunctionEntity(name):
    enlevel=scopeList[-1].enclosing_scope.enlevel
    if not (uniqueEntity(name,'Function',enlevel)):
        ErrorFunc('Not unique entity %s'% name)
    if inFunctionBlock[-1]==True:
        returnType='int'
    else:
        returnType='void'
    scopeList[-2].addEntity(Function(name,returnType))



def addParameterEntity(name,parameterMode):

    enlevel=scopeList[-1].enlevel
    parameterOffset=scopeList[-1].getOffset()

    if not (uniqueEntity(name,'Function',enlevel)):
        ErrorFunc('Not unique entity %s'% name)
    scopeList[-1].addEntity(Parameter(name,parameterMode,parameterOffset))


    
def addVariableEntity(name):

    enlevel = scopeList[-1].enlevel
    variableOffset = scopeList[-1].getOffset()
    if not (uniqueEntity(name, "Variable", enlevel)):
        ErrorFunc('Not unique entity %s'% name)
    if variableExistsAsParameter(name, enlevel):
        ErrorFunc('Already given as parameter %s'% name)
    scopeList[-1].addEntity(Variable(name, variableOffset))



def searchEntity(name,entityType):
    if scopeList ==[]:
        return
    else:
        tempScope=scopeList[-1]
        while tempScope is not None:
            for entity in tempScope.entities:
                if entity.entityType == entityType and  entity.name == name:
                    return entity, tempScope.enlevel
            tempScope = tempScope.enclosing_scope   



def searchEntityWithName(name):
    if scopeList ==[]:
        return
    else:
        tempScope=scopeList[-1]
        while tempScope is not None:
            for entity in tempScope.entities:
                if entity.name == name:
                    return entity, tempScope.enlevel
            tempScope = tempScope.enclosing_scope


def addFunctionArgument(functionName,parameterMode):
    if(parameterMode=='in'):
        newArgument=Argument('CV')
    else:
        newArgument=Argument('REF')
    tempEntity=searchEntity(functionName,"Function")
    functionEntity = tempEntity[0]
    if functionEntity is None:
        ErrorFunc('%s:Entity not found'% functionName)
    if functionEntity.arguments!=[]:
        functionEntity.arguments[-1].setNextArgument(newArgument)
    functionEntity.addArguments(newArgument)  

    

def updateFunctionEntityQuad(name):
    startQuad=nextquad()
    if name==program_name:
        return startQuad
    tempEntity = searchEntity(name,"Function")
    functionEntity = tempEntity[0]
    functionEntity.setStartQuad(startQuad)
    return startQuad

    
def updateFunctionEntityFramelength(name,framelength):
    global mainPFrameLength
    if name== program_name:
        mainPFrameLength=framelength
        return
    tempEntity=searchEntity(name,"Function")
    functionEntity = tempEntity[0]
    functionEntity.setFramelength(framelength)




def uniqueEntity(entity_name,entity_type,entityLevel):
    if scopeList[-1].enlevel< entityLevel:
        return 
    else:
        scope=scopeList[entityLevel]
        for i in range(len(scope.entities)):
            for j in range(len(scope.entities)):
                a1=scope.entities[i]
                a2=scope.entities[j]
                if a1.name==a2.name and a1.entityType==a2.entityType and a1.name==entity_name and a1.entityType==entity_type:
                    return False
                
        return True


def variableExistsAsParameter(name,enlevel):
    if scopeList[-1].enlevel < enlevel:
        return 
    else:
        scope=scopeList[enlevel]
        for i in range(len(scope.entities)):
            a=scope.entities[i]
            if a.name==name and a.entityType=='Parameter':
                return True 
            
        return False


########################################################################

                        #Final code functions

########################################################################

#load $t0 the non-local variable var
def gnvlcode(var):
    if searchEntityWithName(var) is not None:
        tempEntity,tmplevel=searchEntityWithName(var)
    else:
        ErrorFunc('Non declared variable: ' + var)
    if tempEntity.entityType=='Function':
        ErrorFunc('Non declared variable: ' + var)
    currentEnLevel=scopeList[-1].enlevel
    finalfile.write('lw  $t0, -4($sp)\n')
    newEnLevel=currentEnLevel-1-tmplevel
    while newEnLevel!=0 and newEnLevel>0:
        finalfile.write('lw  $t0, -4($t0)\n')
        newEnLevel=newEnLevel-1
    finalfile.write('addi  $t0, $t0, -%d\n' % tempEntity.offset)



def loadvr(var,reg):
    tmp = str(var)
    if tmp.isdigit():
        finalfile.write('li  $t%s, %d\n' % (reg, int(var)))
    else:
        if searchEntityWithName(var) is not None:
            tempEntity, tmplevel=searchEntityWithName(var)
        else:
            ErrorFunc('Non declared variable: ' + var)
        currentEnLevel=scopeList[-1].enlevel
        if tempEntity.entityType == 'Variable' and tmplevel == 0:
            finalfile.write('lw  $t%s, -%d($s0)\n' % (reg, tempEntity.offset))
        elif (tempEntity.entityType == 'Variable' and tmplevel == currentEnLevel) or \
                (tempEntity.entityType == 'Parameter' and tempEntity.parameterMode == 'in' and tmplevel == currentEnLevel) or\
                (tempEntity.entityType == 'TempVariable'):
            finalfile.write('lw  $t%s, -%d($sp)\n' % (reg, tempEntity.offset))
        
        elif tempEntity.entityType == 'Parameter' and tempEntity.parameterMode == 'inout' and tmplevel == currentEnLevel:
            finalfile.write('lw  $t0, -%d($sp)\n' % tempEntity.offset)
            finalfile.write('lw  $t%s, 0($t0)\n' % reg)
        elif (tempEntity.entityType == 'Variable' and tmplevel < currentEnLevel) or \
                (tempEntity.entityType == 'Parameter' and tempEntity.parameterMode == 'in' and tmplevel < currentEnLevel):
            gnvlcode(var)
            finalfile.write('lw  $t%s, 0($t0)\n' % reg)
        elif tempEntity.entityType == 'Parameter' and tempEntity.parameterMode == 'inout' and tmplevel < currentEnLevel:
            gnvlcode(var)
            finalfile.write('lw  $t0, 0($t0)\n')
            finalfile.write('lw  $t%s, 0($t0)\n' % reg)
        else:
            ErrorFunc('loadvr loads data from memory in a register ')

def storerv(reg, var):

    if searchEntityWithName(var) is not None:
        tempEntity, tmplevel=searchEntityWithName(var)
    else:
        ErrorFunc('Non declared variable:' + var) # lathos edo

    currentEnLevel=scopeList[-1].enlevel
    if tempEntity.entityType == 'Variable' and tmplevel == 0:
        finalfile.write('sw  $t%s, -%d($s0)\n' % (reg, tempEntity.offset))
    elif (tempEntity.entityType == 'Variable' and  tmplevel == currentEnLevel) or \
            (tempEntity.entityType == 'Parameter' and tempEntity.parameterMode == 'in' and tmplevel == currentEnLevel) or \
            (tempEntity.entityType == 'TempVariable'):
        finalfile.write('sw  $t%s, -%d($sp)\n' % (reg, tempEntity.offset))
    elif tempEntity.entityType == 'Parameter' and tempEntity.parameterMode == 'inout' and tmplevel == currentEnLevel:
        finalfile.write('lw  $t0, -%d($sp)\n' % tempEntity.offset)
        finalfile.write('sw  $t%s, 0($t0)\n' % reg)
    elif (tempEntity.entityType == 'Variable' and tmplevel < currentEnLevel) or \
            (tempEntity.entityType == 'Parameter' and tempEntity.parameterMode == 'in' and tmplevel < currentEnLevel):

        gnvlcode(var)
        finalfile.write('sw  $t%s, 0($t0)\n' % reg)
    elif tempEntity.entityType == 'Parameter' and tempEntity.parameterMode == 'inout' and tmplevel < currentEnLevel:
        gnvlcode(var)
        finalfile.write('lw  $t0,0(%t0)\n')
        finalfile.write('sw  $t%s, 0($t0)\n' % reg)
    else:
        ErrorFunc('storerv stores data of a register to memory ')


def corvertionToAssemblyCode(quad,blockName):

    global subprogramParams
    if str(quad.label) == '0':
        finalfile.write(' ' * 50) # de ta grafei ola alliws, opote skeftikame na to baloyme na kanei polles fores space prokeimenoy na ta parei
    finalfile.write('\nLine_' + str(quad.label) + ':#' + quad.writeQuadToFile() +'\n')
    
    if quad.op=='jump':
        finalfile.write('j  Line_%d\n' % quad.z)
    elif quad.op in ('=', '<>', '<', '<=', '>', '>='):
        assemblyRelationalOperators=('beq', 'bne', 'blt', 'ble', 'bgt', 'bge')
        relOperators=('=', '<>', '<', '<=', '>', '>=')
        relop = assemblyRelationalOperators[relOperators.index(quad.op)]
        loadvr(quad.x, '1')
        loadvr(quad.y, '2')
        finalfile.write('%s  $t1, $t2, Line_%d\n' % (relop, quad.z)) 
    elif quad.op == ':=':
        loadvr(quad.x, '1')
        storerv('1', quad.z)
    elif quad.op in ('+', '-', '*', '/'):
        assemblyOperators=('add', 'sub', 'mul', 'div')
        op = assemblyOperators[('+', '-', '*', '/').index(quad.op)]
        loadvr(quad.x, '1')
        loadvr(quad.y, '2')
        finalfile.write('%s  $t1, $t1, $t2\n' % op)
        storerv('1', quad.z)       
    elif quad.op=='out':
        loadvr(quad.x, '9') 
        finalfile.write('li  $v0, 1\n')
        finalfile.write('add   $a0, $zero, $t9\n')
        finalfile.write('syscall\n')
    elif quad.op == 'retv':
        loadvr(quad.x, '1')
        finalfile.write('lw  $t0, -8($sp)\n')
        finalfile.write('sw  $t1, 0($t0)\n')
        finalfile.write('lw  $ra, 0($sp)\n')
        finalfile.write('jr  $ra\n')
    elif quad.op == 'halt':
        finalfile.write('li  $v0, 10   # service code 10: exit\n')
        finalfile.write('syscall\n')
    elif quad.op == 'par':
        if blockName==program_name:
            callerLevel=0
            framelength=mainPFrameLength
        else:
            callerEntity,callerLevel=searchEntity(blockName,'Function')
            framelength=callerEntity.framelength
        if subprogramParams == []:
            finalfile.write('addi  $fp, $sp, -%d\n' % framelength)
        subprogramParams.append(quad)
        parameterOffset=12+4*subprogramParams.index(quad)
        if quad.y == 'CV':
            loadvr(quad.x, '0')
            finalfile.write('sw  $t0, -%d($fp)\n' % parameterOffset)
        elif quad.y == 'REF':
            if searchEntityWithName(quad.x) is not None:
                variableEntity, variableLevel = searchEntityWithName(quad.x)
            else:
                ErrorFunc('Non declared variable: ' + quad.x)
            if callerLevel == variableLevel:
                if variableEntity.entityType == 'Variable' or \
                        (variableEntity.entityType == 'Parameter' and variableEntity.parameterMode == 'in'):
                    finalfile.write('addi  $t0, $sp, -%s\n' % variableEntity.offset)
                    finalfile.write('sw   $t0, -%d($fp)\n' % parameterOffset)
                elif variableEntity.entityType == 'Parameter' and variableEntity.parameterMode == 'inout':
                    finalfile.write('lw  $t0, -%d($sp)\n' % variableEntity.offset)
                    finalfile.write('sw  $t0, -%d($fp)\n' % parameterOffset)
            else:
                if variableEntity.entityType == 'Variable' or \
                        (variableEntity.entityType == 'Parameter' and variableEntity.parameterMode == 'in'):
                    gnvlcode(quad.x)
                    finalfile.write('sw  $t0, -%d($fp)\n' % parameterOffset)
                elif variableEntity.entityType == 'Parameter' and variableEntity.parameterMode == 'inout':
                    gnvlcode(quad.x)
                    finalfile.write('lw  $t0, 0($t0)\n')
                    finalfile.write('sw  $t0, -%d($fp)\n' % parameterOffset)
        elif quad.y == 'RET':
            if searchEntityWithName(quad.x)is not None:
                variableEntity, variableLevel = searchEntityWithName(quad.x)
            else:
                ErrorFunc('Non declared variable: ' + quad.x)
            finalfile.write('addi $t0, $sp, -%d\n' % variableEntity.offset)
            finalfile.write('sw  $t0, -8($fp)\n')
    elif quad.op == 'call':
        if blockName == program_name :
            callerLevel = 0
            framelength = mainPFrameLength
        else:
            callerEntity, callerLevel = searchEntity(blockName, 'Function')
            framelength = callerEntity.framelength
        if searchEntity(quad.x, 'Function') is not None:
                calledEntity, calledLevel = searchEntity(quad.x, 'Function')
        else:
                ErrorFunc('Non defined function: ' + quad.x)
        #if subprogram exists get in here###########################################
              
        entity, enlevel = searchEntityWithName(calledEntity.name)
        if entity.returnType == 'int':
            subprogramParams.pop()
        if len(entity.arguments) != len(subprogramParams):
            ErrorFunc('Subprogram %s arguments number not match'% calledEntity.name)
        for argument in entity.arguments:
            quad = subprogramParams.pop(0)
            if not (argument.parameterMode == quad.y):
                if argument.parameterMode == 'CV':
                    parameterType = 'int'
                else:
                    parameterType = 'int *'
                ErrorFunc('%s parameter %s to be of'
                    ' type "%s"' % (name, quad.x, parameterType))

        
        #############################################################################
        if callerLevel == calledLevel:
            finalfile.write('lw  $t0, -4($sp)\n')
            finalfile.write('sw  $t0, -4($fp)\n')
        else:
            finalfile.write('sw  $sp, -4($fp)\n')
        finalfile.write('addi $sp, $sp, -%d\n' % framelength)
        finalfile.write('jal  Line_%s\n' % str(calledEntity.startQuad))
        finalfile.write('addi  $sp, $sp, %d\n' % framelength)      
    elif quad.op == 'begin_block':
        finalfile.write('sw  $ra, 0($sp)\n')
        if blockName == program_name:
            finalfile.seek(0,0)   # start of output file
            finalfile.write('.globl Line_%d\n' % quad.label)
            finalfile.write('j   Line_%d\n' % quad.label)
            finalfile.seek(0,2)   #  end of output file
            finalfile.write('addi $sp, $sp, %d\n' % mainPFrameLength)
            finalfile.write('move $s0, $sp\n')
    elif quad.op == 'end_block':
        if blockName == program_name:
            finalfile.write('j  Line_%d\n' % halt)
        else:
            finalfile.write('lw  $ra, 0($sp)\n')
            finalfile.write('jr  $ra\n')        







###################################################################

            #Parser Functions and grammar implementation

###################################################################
def parser():
    global token, end_of_file
    token=lexicalAnalyzer()
    program() #start syntax analyze
    if end_of_file == 1:
        makeIntermediateCodeFile()
        makeCcodeFile()

    

def program():                # program id { <block>}
    global token, nontoken,program_name, func, scopeList
    if token == "program": #program
        token = lexicalAnalyzer()
        if nontoken == "id": #id
            program_name = token
            token = lexicalAnalyzer()
            if token == "{": # {
                token = lexicalAnalyzer()
                func = program_name
                scopeList.append(Scope())
                block()  # block
                if token != "}": # }
                    ErrorFunc("Expected '}' instead of '" + token +"'.")
                token = lexicalAnalyzer()
            else:
                ErrorFunc("Expected '{' for the program and not '" + token+ "'.")
    else:
        ErrorFunc("keyword 'program' is missing.")

def block(): # decleration subprograms statements
    global func, halt, program_name
    #printScopes()
    tempfunc = func
    declarations()  # declarations
    subprograms()    #subprograms
    blockBeginningQuad=updateFunctionEntityQuad(tempfunc)
    genquad("begin_block",tempfunc,"","")   
    statements()    #statements
    if tempfunc == program_name:
        halt = nextquad()
        genquad('halt')
    genquad('end_block', tempfunc)
    updateFunctionEntityFramelength(tempfunc,scopeList[-1].toffset)
    for quad in quadlist[blockBeginningQuad:]:
        corvertionToAssemblyCode(quad,tempfunc)
    scopeList.pop()
    


def declarations(): # ( declare <varlist>;)*
    global token
    while token == "declare": # )
        token = lexicalAnalyzer()
        varlist()                                # varlist
        if token == ";":
            token = lexicalAnalyzer() # repeats to check if the next is a declare.
        else:
            ErrorFunc("Expected ';' , not '" + token +"'.")


def varlist(): # e|id ( ,id)*
    global token,nontoken
    if nontoken == "id":
        addVariableEntity(token)
        token = lexicalAnalyzer()
        while token == ",":
            token = lexicalAnalyzer()
            if nontoken == "id":
                addVariableEntity(token)
                token = lexicalAnalyzer()
            else:
                ErrorFunc("Expected a variable declaration, not '" +token+"'.")
            

def subprograms(): 
    global token, haveReturn,inFunctionBlock,subprogramExists,func
    while token == "function" or token == "procedure":
        inFunctionBlock.append(False)
        haveReturn.append(False)
        
        subprogramExists=True
        if token == "function" :
            inFunctionBlock[-1]=True
        
        token = lexicalAnalyzer()
        subprogram()
        if inFunctionBlock.pop() ==True:
            if haveReturn.pop()==False:
                ErrorFunc("Expected return from function ")
        else:
            haveReturn.pop()


def subprogram():# function id <funcbody> | procedure id <funcbody>
    global token, nontoken, func
    addNewScope()
    if nontoken == "id":
        func = token 
        token = lexicalAnalyzer()
        addFunctionEntity(func)
        funcbody()
    else:
        ErrorFunc("Expected procedure or function name instead of '" +token+"'.")


def funcbody(): #formalpars { block }
    global token
    formalpars() # formalpars
    if token== "{": # {
        token = lexicalAnalyzer()
        block()                               # block
        if token != "}": # }
            ErrorFunc("Expected '}' and not '" +token+"'.")
        token = lexicalAnalyzer()
    else:
        ErrorFunc("Expected '{' and not '" +token+"'.")


def formalpars():   # (formalparlist)
    global token
    if token == "(": # ( 
        token = lexicalAnalyzer()
        if token == "in" or token == "inout":
            formalparlist() 
        if token != ")": # )
            ErrorFunc("Expected ')' and not '" +token+"'.")
        token = lexicalAnalyzer()
    else:
        ErrorFunc("Expected '(' and not '" +token+"'.")


def formalparlist():# <formalparitem> ( , <formalparitem> )* | e
    global token
    if token == "in" or token == "inout":
        formalparitem() # formalparitem
        while token == ",":
            token = lexicalAnalyzer()
            formalparitem()


def formalparitem():# in id | inout id
    global token,nontoken, func
    if token == "in" or token == "inout": # in | out
        parameterMode=token
        token = lexicalAnalyzer()
        if nontoken != "id": # id
            ErrorFunc("Formal parameter name was expected instead of '"+token+"'.")        
        parameterName=token
        addFunctionArgument(func,parameterMode)
        addParameterEntity(parameterName,parameterMode)
        token = lexicalAnalyzer()



def statements(): #<statement> | { <statement> ( ; <statement> )* }
    global token
    #token = lexicalAnalyzer()
    if token == "{":
        token = lexicalAnalyzer()
        statement() #statement
        while token == ";": #;
            token = lexicalAnalyzer()
            statement()  #statement
        if token != "}":
            ErrorFunc("Expected '}' to close statement(s), but found '"+token+"' instead.")
        token = lexicalAnalyzer()
    else:
        statement()


def statement():
    global token, nontoken, name, haveReturn
    if nontoken == "id":
        tid = token
        token = lexicalAnalyzer()
        assignment_stat()  #assignment_stat
        genquad(":=", name , "_", tid)
    if token == "if": #if-stat
        token = lexicalAnalyzer()
        if_stat()
    elif token == "while": #while-stat
        token = lexicalAnalyzer()
        while_stat()
    elif token == "doublewhile":#doublwhile-stat
        token = lexicalAnalyzer()
        doublewhile_stat()
    elif token == "loop":#loop-stat
        token=lexicalAnalyzer()
        loop_stat()
    elif token == "exit":#exit-stat
        token = lexicalAnalyzer()
        exit_stat()
    elif token == "forcase":#forcase-stat
        token = lexicalAnalyzer() 
        forcase_stat()
    elif token == "incase":#incase-stat
        token = lexicalAnalyzer() 
        incase_stat()
    elif token == "call":#call-stat
        token = lexicalAnalyzer() 
        call_stat()    
    elif token == "return":#return-stat
        if inFunctionBlock!=[] and inFunctionBlock[-1]==True:
            haveReturn[-1]=True
        else:
            ErrorFunc('return out of function')
        token = lexicalAnalyzer()
        return_stat()
    elif token == "input":#input-
        token = lexicalAnalyzer()
        input_stat()
    elif token == "print":#print-stat
        token = lexicalAnalyzer()
        print_stat()


def assignment_stat(): # id := expression
    global token, name
    if token == ":=":
        token = lexicalAnalyzer()
        name = expression()
    else:
        ErrorFunc("Expected ':=' , not '"+token+"'.")


def if_stat(): #if (<condition>) then <statements> <elsepart>
    global token
    if token == "(": # (
        token = lexicalAnalyzer()
        (back_T,back_F) = condition() # condition
        if token != ")":
            ErrorFunc("Expected ')' to close if condition, not '" +token+"'.")
        token = lexicalAnalyzer()
        backpatch(back_T, nextquad())
        skips = makelist(nextquad())
        if token == "then": #then
            genquad("jump")
            backpatch(back_F, nextquad())
            token = lexicalAnalyzer()
            statements() #statements
            elsepart() #elsepart
            backpatch(skips, nextquad())
    else:
        ErrorFunc("Expected '(' after if condition, not '" +token+"'.")


def elsepart(): # else <statements>
    global token
    if token == "else":
        token = lexicalAnalyzer()
        statements()
    else:
        ErrorFunc("Expected 'else' but found '"+token+"'.")


def while_stat(): #while (<condition>) <statements>
    global token
    back_Q = nextquad()
    if token == "(":
        token = lexicalAnalyzer()
        (back_T,back_F) = condition()
        if token != ")":
            ErrorFunc("Expected ')' at the end of while statement, not '" +token+"'.")
        
        token =  lexicalAnalyzer()
        backpatch(back_T, nextquad())
        genquad('jump','_','_',back_Q)
        statements()
        backpatch(back_F,nextquad())
    else:
        ErrorFunc("Expected '(' after while, not '" +token+"'.")


def doublewhile_stat(): #doublewhile (<condition>) <statements> #else <statements>
    global token
    if token == "(":
        token = lexicalAnalyzer()
        condition()
        if token != ")":
            ErrorFunc("Expected ')' at the end of doublewhile statement, not '" +token+"'.")
        token = lexicalAnalyzer()
        statements()
        if token == "else":
            token = lexicalAnalyzer()
            statements()
    else:
        ErrorFunc("Expected '(' at the start of doublewhile statement, not '" +token+"'.")


def loop_stat(): #loop <statements>
    global token
    token = lexicalAnalyzer()
    statements()


def exit_stat():
    global token
    if token == "exit":
        sys._exit()


def forcase_stat():
    global token 
    forcase_list = []
    while token == "when":
        token = lexicalAnalyzer()
        if token != "(":
            ErrorFunc("Expected '(' after when but found '" +token+"'.")
        token = lexicalAnalyzer()
        (back_T,back_F) = condition()
        if token != ")":
            ErrorFunc("Expected ')' at the end of a 'when' condition instead of '"+token+"'.")
        token = lexicalAnalyzer()
        if token != ":":
            ErrorFunc("Expected ':' after the 'when' condition is stated but found '"+token+"'.")
        token = lexicalAnalyzer()
        backpatch(back_T,nextquad())
        statements()
        forcase_list+=makelist(nextquad())
        genquad("jump","","","")
        backpatch(back_F,nextquad())
    if token != "default":
        ErrorFunc("Expected the 'default' keyword instead of '"+token+"'.")
    token = lexicalAnalyzer()
    if token != ":":
        ErrorFunc("Expected the ':' after 'default' keyword instead of '"+token+"'.")
    token = lexicalAnalyzer()
    statements()
    backpatch(forcase_list, nextquad())


def incase_stat():
    global token
    while token == "when":
        token = lexicalAnalyzer()
        if token != "(":
            ErrorFunc("Expected '(' after when but found '" +token+"'.")
        token = lexicalAnalyzer()
        condition()
        if token != ")":
            ErrorFunc("Expected ')' at the end of a 'when' condition instead of '"+token+"'.")
        token = lexicalAnalyzer()
        if token != ":":
            ErrorFunc("Expected ':' after the 'when' condition is stated but found '"+token+"'.")
        token = lexicalAnalyzer()
        statements()


def return_stat(): #return <expression>
    global token
    expr = expression()
    genquad("retv",expr)
    

def call_stat(): #call id <actualpars>
    global token,nontoken
    if nontoken == "id":
        procedureId=token
        token = lexicalAnalyzer()
        actualpars()
        if searchEntityWithName(procedureId) is None:
            ErrorFunc('Non defined procedure'% procedureId)
        else:
            procedure,procedureLevel= searchEntityWithName(procedureId)
        genquad('call',procedureId)
    else:
        ErrorFunc("The call procedure isn't defined.")


def print_stat(): #print (<expression>)
    global token
    if token == "(":
        token = lexicalAnalyzer()
        printexp = expression()
        genquad("out",printexp)
        if token != ")":
            ErrorFunc("Expected ')' at the end of a 'print' expression instead of '"+token+"'.")
        token = lexicalAnalyzer()
    else:
        ErrorFunc("Expected '(' to print an expression instead of '"+token+"'.")


def input_stat(): #input (id)
    global token,nontoken
    if token=="(": #(
        token = lexicalAnalyzer()
        if nontoken == "id": #id
            token  = lexicalAnalyzer()        
            if token!=")": #)
                ErrorFunc("Expected ')' after an input is given, not '"+token+"'.")
            token = lexicalAnalyzer()
        else:
            ErrorFunc("Expected an input to be given instead of '"+token+"'.")
    else:
        ErrorFunc("Expected '(' after 'input' to define the input given but found '"+token+"'.")


def actualpars():# ( <actualparlist> )
    global token
    if token == "(":
        token = lexicalAnalyzer()
        if token == "in" or token == "inout":
            actualparlist()
        if token != ")":
            ErrorFunc("Expected ')' after an input is given, not '"+token+"'.")
        token = lexicalAnalyzer()
        return True
    else:
        ErrorFunc("Expected '(' after procedure or function name instead of '" +token+"'.")


def actualparlist(): #<actualparitem> ( , <actualparitem> )* | e
    global token
    actualparitem()
    while token == ",":
        token = lexicalAnalyzer()
        actualparitem()


def actualparitem(): #in <expression> | inout id
    global token, nontoken
    if token == "in": # in
        token = lexicalAnalyzer()
        expr = expression()
        genquad("par", expr , "CV")
    elif token == "inout": #out
        token = lexicalAnalyzer()
        if nontoken != "id": #id
            ErrorFunc("Id variable was expected instead of '"+token+"'.")
        tid = token
        token = lexicalAnalyzer()
        genquad("par", tid , "REF")
    else:
        ErrorFunc("A parameter type was expected, for example 'in' or 'inout', but found '"+token+"'.")


def condition(): #<boolterm> (or <boolterm>)*
    global token
    (back_T1,back_F1) = boolterm()
    (cond_T,cond_F) = (back_T1,back_F1)
    while token == "or":
        backpatch(cond_F, nextquad())
        token = lexicalAnalyzer()
        (back_T2, back_F2) = boolterm()
        cond_T = mergelist(cond_T,back_T2)
        cond_F = back_F2
    return cond_T, cond_F



def boolterm(): #<boolfactor> (and <boolfactor>)*
    global token
    (back_T1,back_F1) = boolfactor()
    (bool_T,bool_F) = (back_T1,back_F1)
    while token == "and":
        backpatch(bool_T,nextquad())
        token = lexicalAnalyzer()
        (back_T2,back_F2) = boolfactor()
        bool_T = back_T2
        bool_F = mergelist(bool_F,back_F2)
    return bool_T,bool_F


def boolfactor(): #not [<condition>] | [<condition>] |
#<expression> <relational-oper> <expression>
    global token
    if token == "not":
        token = lexicalAnalyzer()
        if token == "[":
            token = lexicalAnalyzer()
            truth_lists = condition()
            truth_lists = truth_lists[::-1]
            if token != "]":
                ErrorFunc("Expected ']' instead of '"+token+"'.")
            token = lexicalAnalyzer()
        else:
            ErrorFunc("Expected '[' instead of '"+token+"'.")
    elif token == "[":
        token = lexicalAnalyzer()
        condition()
        if token != "]":
            ErrorFunc("Expected ']' instead of '"+token+"'.")
        token = lexicalAnalyzer()
    else:
            expr1= expression()
            oper = relational_oper()
            expr2=expression()
            l_true=makelist(nextquad())
            genquad(oper,expr1,expr2)
            l_false=makelist(nextquad())
            genquad('jump')
            truth_lists=(l_true,l_false)
    return truth_lists


def expression(): #<optional-sign> <term> ( <add-oper> <term>)*
    global token
    op = optional_sign()
    term1=term()
    if op is not None:
        stemp=newTemp()
        genquad('-',0,term1,stemp)
        term1=stemp
        
    while token == "+" or token == "-":
        op = add_oper()
        term2= term()
        TmpVariable=newTemp()
        genquad(op,term1,term2,TmpVariable)
        term1=TmpVariable
    return term1


def term(): #<factor> (<mul-oper> <factor>)*
    global token
    factor1=factor()
    while token == "*" or token == "/":
        operator=mul_oper()
        factor2= factor()
        TmpVariable=newTemp()
        genquad(operator,factor1,factor2,TmpVariable)
        factor1=TmpVariable
    return factor1


def idtail():# e | <actualpars>
    global token
    if token == "(":
        return actualpars()


def factor():  #constant | (<expression>) | id <idtail>
    global token, nontoken
    value = 0
    if nontoken == "number" :
        if(abs(float(token)>32767)):
            ErrorFunc("Constant is not within the range of [-32767,32767].")
        value = token
        token = lexicalAnalyzer() 
    elif token == "(":
        token  = lexicalAnalyzer()
        value = expression()
        if token != ")":
            ErrorFunc("Expected ')' instead of '"+token+"'.")
        token = lexicalAnalyzer()
    elif nontoken == "id":
        value=token
        token = lexicalAnalyzer()
        tid = idtail()
        if tid is not None:
            tempret=newTemp()
            genquad('par',tempret,'RET')
            if searchEntityWithName(value) is None:
                ErrorFunc('Non defined procedure '% value)
            else:
                facto,factorLevel = searchEntityWithName(value)
            genquad('call',value)
            value=tempret
    else:
        ErrorFunc("Expected factor instead of '"+token+"'.")
    return value



def relational_oper():
    global token
    op = token
    if token != "=" and token != "<" and \
            token != ">" and token != "<>" and \
            token != ">=" and token != "<=":
        ErrorFunc("A relation operator was expected, not '"+token+"'.")
    token = lexicalAnalyzer()
    return op

def add_oper(): #+ | -
    global token
    op = token
    if token != "+" and token != "-":
        ErrorFunc("Expected '+' or '-' instead of '"+token+"'.")
    token = lexicalAnalyzer()
    return op

def mul_oper(): #* | /
    global token
    op = token
    if token != "*" and token != "/":
        ErrorFunc("Expected '*' or '/' instead of '"+token+"'.")
    token = lexicalAnalyzer()
    return op

def optional_sign(): #e | <add-oper>
    global token
    if token == "+" or token == "-":
        return add_oper()

        
    
def main(argv):
    global infile, showfile, c_file, int_file, finalfile
    path = os.getcwd()
    infile = "empty" # No inputfile yet given
    try:
        opts, args = getopt.getopt(argv, "hi:o",["infile="])#, ["help", "output="])
    except getopt.GetoptError as err:
        # print help information and exit:
        print(str("Enter an input file. I.E: minimal++.py -i 'inputfile_name'"))  # will print something like "option -a not recognized"
        sys.exit(2)
    for opt, arg in opts:
        if opt in ("-h", "--help"):
            print(str("This is an example: minimal++.py -i 'inputfile_name'"))  # will print something like "option -a not recognized"
            sys.exit()
        elif opt in ("-i", "--input"):
            infile = arg
        else:
            assert False, "unhandled option"
    print("Inputfile given is " + infile + ".")

    try:
        os.mkdir(path+"/cOutputs/")
        os.mkdir(path+"/intOutputs/")
        os.mkdir(path+"/asmOutputs/")
    except OSError:
        print ("Creation of the directory %s failed" % path)
    else:
        print ("Successfully created the directory %s " % path)



    file_name = infile.split(".")
    int_file_name = file_name[0] + ".int"
    int_file_name = path+"/intOutputs/"+int_file_name

    c_file_name = file_name[0]   + ".c"
    c_file_name = path+"/cOutputs/"+c_file_name

    finalfile = file_name[0] + ".asm"
    finalfile = path+"/asmOutputs/"+finalfile
    c_file = open(c_file_name,'w', encoding ='utf-8')
    int_file = open(int_file_name,'w', encoding = 'utf-8')
    finalfile = open(finalfile,'w', encoding = 'utf-8')
    if infile !="empty":
        print("Inputfile given is " + infile + ".")
        print("Inputfile Detected. Commencing Syntax Analysis")
        try:
            showfile = open(infile, mode='r')
        except:
            print("No such file in directory. Please give a viable inputfile")
            sys.exit(0)
        parser() # file is closed inside lexical analyzer in the EOF state

    showfile.close()
    c_file.close()
    int_file.close()
    finalfile.close()    
    print("\n======COMPLETE======")
    print("Syntax Analysis was successful!")
if __name__ == "__main__":
    main(sys.argv[1:])
                
