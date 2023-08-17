from z3 import *
import sys

# converting input into a list inputtext
inputtext = []
lines = -1
with open(sys.argv[1]) as f:
    contents = f.read()
    contents.strip()
    for entry in contents.split('\n'):
        lines += 1
        inputtext.append(entry.split(','))

# Object Car
class Car:
    def __init__(self, r1, c1, r2, c2):
        self.r1 = r1
        self.c1 = c1
        self.r2 = r2
        self.c2 = c2
# Object Mine
class Mine:
    def __init__(self, r1, c1):
        self.r1 = r1
        self.c1 = c1

# List of Objects in grid
H_Cars=[]
V_Cars=[]
Mines=[]

i=int(inputtext[1][0])
j=int(inputtext[1][1])
H_Cars.append(Car(i,j,i,j+1))

for line in range(2,lines):
    i=int(inputtext[line][1])
    j=int(inputtext[line][2])
    if int(inputtext[line][0])==0:
        V_Cars.append(Car(i,j,i+1,j))
    if int(inputtext[line][0])==1:
        H_Cars.append(Car(i,j,i,j+1))
    if int(inputtext[line][0])==2:
        Mines.append(Mine(i,j))

# Initialising Parameters
n=int(inputtext[0][0])
turns=int(inputtext[0][1])+1
# turns=10
idH = len(H_Cars)
idV = len(V_Cars)
idM = len(Mines)

HSumForGrid=[]
VSumForGrid=[]

for i in range(n):
    HSumForGrid.append(0)
    VSumForGrid.append(0)

for car in H_Cars:
    HSumForGrid[car.r1]+=2
    
for car in V_Cars:
    VSumForGrid[car.c1]+=2

s = Solver()

# condition that red car has no horizontal car in front
for car in H_Cars:
        if car.r1==H_Cars[0].r1 and car.c1 > H_Cars[0].c1:
            print("unsat")
            sys.exit()
        
# G = [[[Int("g_%i_%i_%i" % (turn,i,j))for j in range(n)]for i in range(n)]for turn in range(turns)]
v_bool = [[[Bool("v_%i_%i_%i" % (turn,i,j))for j in range(n)]for i in range(n)]for turn in range(turns)]
h_bool = [[[Bool("h_%i_%i_%i" % (turn,i,j))for j in range(n)]for i in range(n)]for turn in range(turns)]
m_bool = [[Bool("m_%i_%i" % (i,j))for j in range(n)]for i in range(n)]

# Start Initial state
Set=set()
for mine in Mines:
    Set.add((mine.r1,mine.c1))
for i in range(n):
        for j in range(n):
            if (i,j) in Set:
                s.add(m_bool[i][j])
                for turn in range(turns):
                    s.add(Not(h_bool[turn][i][j]))
                    s.add(Not(v_bool[turn][i][j]))
            else:
                s.add(Not(m_bool[i][j]))

for car in H_Cars:
    s.add(h_bool[0][car.r1][car.c1]) 
    s.add(h_bool[0][car.r2][car.c2])
    
    s.add(Not(v_bool[0][car.r1][car.c1]))
    s.add(Not(v_bool[0][car.r2][car.c2]))
    
for car in V_Cars:
    s.add(v_bool[0][car.r1][car.c1]) 
    s.add(v_bool[0][car.r2][car.c2])
    
    s.add(Not(h_bool[0][car.r1][car.c1])) 
    s.add(Not(h_bool[0][car.r2][car.c2]))
# End Initial State

for turn in range(turns-1):
    condition_list = []
    # only one thing in a cell
    for i in range(n):
        for j in range(n):
            temp=[v_bool[turn][i][j], h_bool[turn][i][j], m_bool[i][j]]
            condition_list.append(AtMost(*temp,1))

    # Sum of things in a row/column remain same
    for i in range(n):
        temp=[h_bool[turn][i][j] for j in range(n)]
        condition_list.append(AtLeast(*temp,HSumForGrid[i]))
        condition_list.append(AtMost(*temp,HSumForGrid[i]))
    for j in range(n):
        temp=[v_bool[turn][i][j] for i in range(n)]
        condition_list.append(AtLeast(*temp,VSumForGrid[j]))
        condition_list.append(AtMost(*temp,VSumForGrid[j]))

    # cars stick together
    for i in range(n):
        for j in range(1,n-1):
            condtn=h_bool[turn][i][j]
            rslt=Or(h_bool[turn][i][j-1],h_bool[turn][i][j+1])
            condition_list.append(Implies(condtn,rslt))
        # edge condition
        condtn=h_bool[turn][i][0]
        rslt=h_bool[turn][i][1]
        condition_list.append(Implies(condtn,rslt))
        condtn=h_bool[turn][i][n-1]
        rslt=h_bool[turn][i][n-2]
        condition_list.append(Implies(condtn,rslt))

    # cars stick together
    for i in range(1,n-1):
        for j in range(n):
            condtn=v_bool[turn][i][j]
            rslt=Or(v_bool[turn][i-1][j],v_bool[turn][i+1][j])
            condition_list.append(Implies(condtn,rslt))
        # edge condition
            condtn=v_bool[turn][0][j]
            rslt=v_bool[turn][1][j]
            condition_list.append(Implies(condtn,rslt))
            condtn=v_bool[turn][n-1][j]
            rslt=v_bool[turn][n-2][j]
            condition_list.append(Implies(condtn,rslt))

    # Only one move per turn
    temp=[Not(v_bool[turn][i][j]==v_bool[turn+1][i][j]) for i in range(n) for j in range(n)]
    Bit1C = And(AtMost(*temp,2),AtMost(*temp,2))
    temp=[Not(h_bool[turn][i][j]==h_bool[turn+1][i][j]) for i in range(n) for j in range(n)]
    Bit2C = And(AtMost(*temp,2),AtLeast(*temp,2))
    Bit1N = And([(v_bool[turn][i][j]==v_bool[turn+1][i][j]) for i in range(n) for j in range(n)])
    Bit2N = And([(h_bool[turn][i][j]==h_bool[turn+1][i][j]) for i in range(n) for j in range(n)])
    
    X=And(Bit1C,Bit2N)
    Y=And(Bit1N,Bit2C)
    condition_list.append(Or(X,Y))
    condition_list.append(Or(Not(X),Not(Y)))


    # multiple cars dont move together
    movelist=[]
    for i in range(n):
        for j in range(n-2):
            X=Not(h_bool[turn][i][j] == h_bool[turn+1][i][j])
            Y=Not(h_bool[turn][i][j+2] == h_bool[turn+1][i][j+2])
            movelist.append(And(X,Y))
    for j in range(n):
        for i in range(n-2):
            X=Not(v_bool[turn][i][j] == v_bool[turn+1][i][j])
            Y=Not(v_bool[turn][i+2][j] == v_bool[turn+1][i+2][j])
            movelist.append(And(X,Y))
    s.add(AtMost(*movelist,1))
    s.add(AtLeast(*movelist,1))



    if turn>0:
        s.add(Or(h_bool[turn-1][H_Cars[0].r1][n-1],And(condition_list)))
    else:
        s.add(And(condition_list))


# 
#!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! 
# 

for turn in range(turns-1,turns):
    # only one thing in a cell
    for i in range(n):
        for j in range(n):
            temp=[v_bool[turn][i][j], h_bool[turn][i][j], m_bool[i][j]]
            s.add(AtMost(*temp,1))

    # Sum of things in a row/column remain same
    for i in range(n):
        temp=[h_bool[turn][i][j] for j in range(n)]
        s.add(AtLeast(*temp,HSumForGrid[i]))
        s.add(AtMost(*temp,HSumForGrid[i]))
    for j in range(n):
        temp=[v_bool[turn][i][j] for i in range(n)]
        s.add(AtLeast(*temp,VSumForGrid[j]))
        s.add(AtMost(*temp,VSumForGrid[j]))

    # cars stick together
    for i in range(n):
        for j in range(1,n-1):
            condtn=h_bool[turn][i][j]
            rslt=Or(h_bool[turn][i][j-1],h_bool[turn][i][j+1])
            s.add(Implies(condtn,rslt))
        # edge condition
        condtn=h_bool[turn][i][0]
        rslt=h_bool[turn][i][1]
        s.add(Implies(condtn,rslt))
        condtn=h_bool[turn][i][n-1]
        rslt=h_bool[turn][i][n-2]
        s.add(Implies(condtn,rslt))

    # cars stick together
    for i in range(1,n-1):
        for j in range(n):
            condtn=v_bool[turn][i][j]
            rslt=Or(v_bool[turn][i-1][j],v_bool[turn][i+1][j])
            s.add(Implies(condtn,rslt))
        # edge condition
            condtn=v_bool[turn][0][j]
            rslt=v_bool[turn][1][j]
            s.add(Implies(condtn,rslt))
            condtn=v_bool[turn][n-1][j]
            rslt=v_bool[turn][n-2][j]
            s.add(Implies(condtn,rslt))

# win condition
s.add(Or([(h_bool[turn][H_Cars[0].r1][n-1])for turn in range(turns)]))

s.check()

try:
    m=s.model()
except:
    print("unsat")
else:
    No_of_turns=-1
    for turn in range(turns):
        if m.evaluate(h_bool[turn][H_Cars[0].r1][n-1])==True:
            No_of_turns=turn
            break

    # Grid printing
    for turn in range(No_of_turns):
        o=[]
        for i in range(n):
            for j in range(n):
                if not m.evaluate(h_bool[turn][i][j])==m.evaluate(h_bool[turn+1][i][j]):
                    o.append([i,j])
                if not m.evaluate(v_bool[turn][i][j])==m.evaluate(v_bool[turn+1][i][j]):
                    o.append([i,j])
        print(int((o[0][0]+o[1][0])/2),end="")
        print(",",end="")
        print(int((o[0][1]+o[1][1])/2))