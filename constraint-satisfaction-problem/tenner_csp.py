#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the warehouse domain.  

'''
Construct and return Tenner Grid CSP models.
'''

from cspbase import *
import itertools
import numpy

#def rowCheck(row, val):
#   for item in row:
#        if item.domain_size() == 1: #preset values
#            ind = row.index(item)
#            preset_val = item.domain()[0]
#            if val[ind] != preset_val:
#                return False
#    return True
def rowCheck(row, val):
    for item in row:
        if item.domain_size() == 1:
            ind = row.index(item)
            preset_val = item.domain()[0]
            if val[ind] != preset_val:
                return False
    return True

def binaryNQ(ti,tj,vali,valj):
    #print((ti,tj,vali,valj))
    ci = int(ti.name[2])
    ri = int(ti.name[1])
    cj = int(tj.name[2])
    rj = int(tj.name[1])
    #print(ri,ci,rj,cj)
    if ri == rj and vali == valj: 
        return False
    elif abs(rj - ri)==1 and abs(cj - ci)==1 and (vali == valj):#diagnal
        return False
    elif (ci == cj) and abs(rj - ri)==1 and (vali == valj): #same column && adjacent
        return False 
    else:
        return True
        
def binaryNQ1(ti,tj,vali,valj):
    #print((ti,tj,vali,valj))
    ci = int(ti.name[2])
    ri = int(ti.name[1])
    cj = int(tj.name[2])
    rj = int(tj.name[1])
    #print(ri,ci,rj,cj)
    #if ri == rj and vali == valj: 
    #    return False
    if (ci == cj) and abs(rj - ri)== 1 and (vali == valj): #same column && adjacent
        return False 
    if abs(rj - ri)==1 and abs(cj - ci)==1 and (vali == valj):#diagnal
        return False
    else:
        return True
        
def checkNeighb(board, val,t):
    index = 0
    for e in val:
        r = int(t[index].name[1])
        c = int(t[index].name[2])
        neighb = set(neighbors(board)(r,c))
        neighb.remove(-1)
        index += 1
        if e in neighb:
            return False
    return True
        
        
def neighbors(grid):
    X = grid.shape[0]
    Y = grid.shape[1]
    neighbors = lambda x, y : [grid[x2,y2] for x2 in range(x-1, x+2)
                                for y2 in range(y-1, y+2)
                                if (-1 < x <= X and
                                    -1 < y <= Y and
                                    (x != x2 or y != y2) and
                                    (0 <= x2 < X) and
                                    (0 <= y2 < Y))]
    return neighbors
    
def make(num_lis, val, raw_d, row):
    temp_dom = raw_d.copy()
    temp_dic = dict()
    
    num_lis.sort()
    for num in num_lis:
        temp_dic[val.index(num)] = num
        temp_dom.remove(num)
    return temp_dic, temp_dom

def tenner_csp_model_1(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along 
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner grid using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from 
       (0,0) to (n,9)) where n can be 3 to 8.
       
       
       The input board is specified as a pair (n_grid, last_row). 
       The first element in the pair is a list of n length-10 lists.
       Each of the n lists represents a row of the grid. 
       If a -1 is in the list it represents an empty cell. 
       Otherwise if a number between 0--9 is in the list then this represents a 
       pre-set board position. E.g., the board
    
       ---------------------  
       |6| |1|5|7| | | |3| |
       | |9|7| | |2|1| | | |
       | | | | | |0| | | |1|
       | |9| |0|7| |3|5|4| |
       |6| | |5| |0| | | | |
       ---------------------
       would be represented by the list of lists
       
       [[6, -1, 1, 5, 7, -1, -1, -1, 3, -1],
        [-1, 9, 7, -1, -1, 2, 1, -1, -1, -1],
        [-1, -1, -1, -1, -1, 0, -1, -1, -1, 1],
        [-1, 9, -1, 0, 7, -1, 3, 5, 4, -1],
        [6, -1, -1, 5, -1, 0, -1, -1, -1,-1]]
       
       
       This routine returns model_1 which consists of a variable for
       each cell of the board, with domain equal to {0-9} if the board
       has a -1 at that position, and domain equal {i} if the board has
       a fixed number i at that cell.
       
       model_1 contains BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.).
       model_1 also constains n-nary constraints of sum constraints for each 
       column.
    '''


        
    raw_d = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] # init
    n_grid = numpy.array(initial_tenner_board[0])
    r = n_grid.shape[0]
    c = n_grid.shape[1]
    array = [[tuple() for i in range(c)] for j in range(r)] 
        
    i = 0
    for row in initial_tenner_board[0]:
        j = 0
        for val in row:
            if val == -1: # empty
                array[i][j] = Variable('V{}{}'.format(i,j), raw_d)
            else:
                array[i][j] = Variable('V{}{}'.format(i,j), [val])
            j += 1
        i += 1  
        
    variable_array = []
    [[variable_array.append(row[i])for i in range(len(array[0])) ]for row in array]
      
    cons = []    
    for ti in range(len(variable_array)):
        for tj in range(ti+1, len(variable_array)):
            con = Constraint("C1(V{},V{})".format(ti,tj),[variable_array[ti], variable_array[tj]]) 
            sat_tuples = []
            for val in itertools.product(raw_d, raw_d):#every possible values in variables
                if binaryNQ(variable_array[ti], variable_array[tj], val[0], val[1]):
                    sat_tuples.append(val)
            con.add_satisfying_tuples(sat_tuples)
            cons.append(con)
            
    for t in range(c):# for every column
        col = [array[i][t] for i in range(r)]
        con = Constraint("C2(V{})".format(str(t)),col)#constraint scope
        sat_tuples = []        
        for val in itertools.product(raw_d, repeat = r):#satified tuples
            if sum(val) == initial_tenner_board[1][t]:
                sat_tuples.append(val)
        con.add_satisfying_tuples(sat_tuples)
        cons.append(con)
        
        
    csp = CSP("TENNER-M{}".format(1), variable_array) 
    for c in cons:
        csp.add_constraint(c)

    return csp,array


def tenner_csp_model_2(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along 
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from 
       (0,0) to (n,9)) where n can be 3 to 8.

       The input board takes the same input format (a list of n length-10 lists
       specifying the board as tenner_csp_model_1.
    
       The variables of model_2 are the same as for model_1: a variable
       for each cell of the board, with domain equal to {0-9} if the
       board has a -1 at that position, and domain equal {i} if the board
       has a fixed number i at that cell.

       However, model_2 has different constraints. In particular,
       model_2 has a combination of n-nary 
       all-different constraints and binary not-equal constraints: all-different 
       constraints for the variables in e    #for ti in range(len(variable_array)):
        #for tj in range(ti+1, len(variable_array)):
            #con = Constraint("C1(V{},V{})".format(ti,tj),[variable_array[ti], variable_array[tj]]) 
            #sat_tuples = []
            #for val in itertools.product(raw_d, raw_d):#every possible values in variables
                #if binaryNQ1(variable_array[ti], variable_array[tj], val[0], val[1]) and :
                    #sat_tuples.append(val)
        #con.add_satisfying_tuples(sat_tuples)
        #cons.append(con) ach row, binary constraints for  
       contiguous cells (including diagonally contiguous cells), and n-nary sum 
       constraints for each column. 
       Each n-ary all-different constraint has more than two variables (some of 
       these variables will have a single value in their domain). 
       model_2 should create these all-different constraints between the relevant 
       variables.
    '''

    raw_d = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] # init
    n_grid = numpy.array(initial_tenner_board[0])
    r = n_grid.shape[0]
    c = n_grid.shape[1]
    array = [[tuple() for i in range(c)] for j in range(r)] 
        
    i = 0
    for row in initial_tenner_board[0]:
        j = 0
        for val in row:
            if val == -1: # empty
                array[i][j] = Variable('V{}{}'.format(i,j), raw_d)
            else:
                array[i][j] = Variable('V{}{}'.format(i,j), [val])
            j += 1
        i += 1
        
    variable_array = []
    [[variable_array.append(row[i]) for i in range(len(array[0])) ] for row in array]
   
    cons = []  

    #for ti in range(r):#for every row
        #row = [array[ti][j] for j in range(c)]
        #temp_dom = []
        #temp_dic = {}
        #r_cp = row.copy() 
        #row_val = list(n_grid[ti])
        #num_lis = []
        #for item in row:
            #if item.domain_size() != 10: #preset values
                #num_lis.append(item.domain()[0])
                #r_cp.remove(item)
        #temp_dic, temp_dom = make(num_lis, row_val, raw_d, row)
        
        #con = Constraint("C1(V_row{})".format(str(ti)),row)
        #sat_tuples = [] 
        #for val in itertools.permutations(temp_dom, len(temp_dom)):#satified tuples
            #if checkNeighb(n_grid, val, r_cp):
            #val = list(val)
            #for item in temp_dic.keys():
                #val.insert(item , temp_dic[item])
            #sat_tuples.append(tuple(val))
        #con.add_satisfying_tuples(sat_tuples)
        #cons.append(con)  

    for ti in range(r):
        row = [array[ti][j] for j in range(c)]
        con = Constraint("C3(V_row{})".format(str(ti)),row)
        sat_tuples = [] 
        for val in itertools.permutations(raw_d, len(raw_d)):#satified tuples
            if rowCheck(row, val): #and checkNeighb(n_grid, val, row):
                sat_tuples.append(val)
        con.add_satisfying_tuples(sat_tuples)
        cons.append(con) 
                
   
    for ti in range(len(variable_array)):
        for tj in range(ti+1, len(variable_array)):
            con = Constraint("C1(V{},V{})".format(ti,tj),[variable_array[ti], variable_array[tj]]) 
            sat_tuples = []
            for val in itertools.product(variable_array[ti].domain(), variable_array[tj].domain()):#every possible values in variables
                if binaryNQ1(variable_array[ti], variable_array[tj], val[0], val[1]):
                    sat_tuples.append(val)
            con.add_satisfying_tuples(tuple(sat_tuples))
            cons.append(con)

    '''for i in range(len(array)):
        for j in range(len(array[i])-1):
            for k in (j-1,j,j+1):
                if k >=0 and k<len(array[i]):
                    con = Constraint("C1(V{},V{})".format(i,j),[array[i][j],array[i+1][k]])
                    sat_tuples = []
                    for val in itertools.product(array[i][j].domain(), array[i+1][k].domain()):
                        if val[0] not == val[1]:
                            sat_tuples.append(val)
                    con.add_satisfying_tuples(tuple(sat_tuples))
                    cons.append(con)'''
                    
            

    for t in range(c):# for every column
        col = [array[i][t] for i in range(r)]
        con = Constraint("C2(V_col{})".format(str(t)),col)#constraint scope
        sat_tuples = []        
        for val in itertools.product(raw_d, repeat = r):#satified tuples
            if sum(val) == initial_tenner_board[1][t]:
                sat_tuples.append(val)
        con.add_satisfying_tuples(sat_tuples)
        cons.append(con)
         
        
    csp = CSP("TENNER-M{}".format(2), variable_array) 
    for c in cons:
        csp.add_constraint(c)

    return csp,array
