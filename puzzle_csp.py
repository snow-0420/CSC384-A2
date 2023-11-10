#Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of Variable objects
representing the board. The returned list of lists is used to access the
solution.

For example, after these three lines of code

    csp, var_array = caged_csp_model(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the FunPuzz puzzle.

The grid-only models do not need to encode the cage constraints.

1. binary_ne_grid (worth 10/100 marks)
    - A model of a FunPuzz grid (without cage constraints) built using only
      binary not-equal constraints for both the row and column constraints.

2. nary_ad_grid (worth 10/100 marks)
    - A model of a FunPuzz grid (without cage constraints) built using only n-ary
      all-different constraints for both the row and column constraints.

3. caged_csp_model (worth 25/100 marks)
    - A model built using your choice of (1) binary binary not-equal, or (2)
      n-ary all-different constraints for the grid.
    - Together with FunPuzz cage constraints.

'''
from cspbase import *
import itertools

def binary_ne_grid(fpuzz_grid):
    size = fpuzz_grid[0][0]
    var_list = []
    var_array = []
    const_list = []
    for i in range(1, size + 1):
        row = []
        for j in range(1, size + 1):
            var = Variable('c{0}{1}'.format(i, j), [*range(1, size + 1)])
            var_list.append(var)
            row.append(var)
            if j > 1: # If not leftmost, can add binary neq towards all leftward cells
                for k in range(1, j):
                    const = Constraint('BNE {0}{1} and {2}{3}'.format(i, k, i, j), [var_list[(i-1)*size + (k-1)], var_list[(i-1)*size + (j-1)]])
                    sat_tuple = []
                    for t in itertools.product([*range(1, size+1)], [*range(1, size+1)]):
                        if t[0] != t[1]:
                            sat_tuple.append(t)
                    const.add_satisfying_tuples(sat_tuple)
                    const_list.append(const)
            if i > 1: # If not upmost, can add binary neq towards all upper cells
                for k in range(1, i):
                    const = Constraint('BNE {0}{1} and {2}{3}'.format(k, j, i, j), [var_list[(k-1)*size + (j-1)], var_list[(i-1)*size + (j-1)]])
                    sat_tuple = []
                    for t in itertools.product([*range(1, size+1)], [*range(1, size+1)]):
                        if t[0] != t[1]:
                            sat_tuple.append(t)
                    const.add_satisfying_tuples(sat_tuple)
                    const_list.append(const)
        var_array.append(row)
    csp = CSP('Binary Not Equal Grid', var_list)
    for const in const_list:
        csp.add_constraint(const)
    return csp, var_array


def nary_ad_grid(fpuzz_grid):
    size = fpuzz_grid[0][0]
    var_list = []
    var_array = []
    const_list = []
    for i in range(1, size + 1):
        row = []
        for j in range(1, size + 1):
            var = Variable('c{0}{1}'.format(i, j), [*range(1, size + 1)])
            var_list.append(var)
            row.append(var)
        const = Constraint('AD for row {0}'.format(i), row)
        varDoms = []
        for v in row:
            varDoms.append(v.domain())
        sat_tuple = []
        for t in itertools.product(*varDoms):
            if all_diff(t):
                sat_tuple.append(t)
        const.add_satisfying_tuples(sat_tuple)
        const_list.append(const)
        var_array.append(row)
    for i in range(size): # for column constraints
        column = []
        for j in range(size):
            column.append(var_array[j][i])
        const = Constraint('AD for column {0}'.format(i+1), column)
        varDoms = []
        for v in column:
            varDoms.append(v.domain())
        sat_tuple = []
        for t in itertools.product(*varDoms):
            if all_diff(t):
                sat_tuple.append(t)
        const.add_satisfying_tuples(sat_tuple)
        const_list.append(const)
    csp = CSP('N-ary All Diff Grid', var_list)
    for const in const_list:
        csp.add_constraint(const)
    return csp, var_array

def all_diff(lst):
    for i in range(len(lst)):
        for j in range(i+1, len(lst)):
            if lst[i] == lst[j]:
                return False
    return True

def caged_csp_model(fpuzz_grid):
    size = fpuzz_grid[0][0]
    csp, var_array = nary_ad_grid(fpuzz_grid)
    for cage in fpuzz_grid[1:]:
        op = cage[-1] # which operation
        target = cage[-2]
        varDoms = []
        cage_var_lst = []
        for var in cage[:-2]:
            row, column = int(str(var)[0]), int(str(var)[1])
            cage_var_lst.append(var_array[row-1][column-1])
        for v in cage_var_lst:
            varDoms.append(v.domain())
        sat_tuple = []
        if op == 0: # addition
            const = Constraint('Addition Cage', cage_var_lst)
            for t in itertools.product(*varDoms):
                if sum(t) == target:
                    sat_tuple.append(t)
        elif op == 1: # subtraction
            const = Constraint('Subtraction Cage', cage_var_lst)
            for t in itertools.product(*varDoms):
                if cage_subtraction(t, target):
                    sat_tuple.append(t)
        elif op == 2: # division
            const = Constraint('Division Cage', cage_var_lst)
            for t in itertools.product(*varDoms):
                if cage_division(t, target):
                    sat_tuple.append(t)
        else: # multiplication
            const = Constraint('Multiplication Cage', cage_var_lst)
            for t in itertools.product(*varDoms):
                if lst_mult(t) == target:
                    sat_tuple.append(t)
        const.add_satisfying_tuples(sat_tuple)
        csp.add_constraint(const)
    return csp, var_array

def cage_subtraction(lst, target):
    for i in range(len(lst)):
        num = lst[i]
        sub_lst = [-x for x in lst]
        sub_lst[i] = num
        if sum(sub_lst) == target:
            return True
    return False

def cage_division(lst, target):
    perm_lst = itertools.permutations(lst)
    for sub_lst in perm_lst:
        if lst_division(sub_lst) == target:
            return True
    return False

def lst_division(lst):
    num = lst[0]
    for i in lst[1:]:
        num = num / i
    return num

def lst_mult(lst):
    num = 1
    for i in lst:
        num = num * i
    return num
