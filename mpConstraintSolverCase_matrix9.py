'''
Author: Uzio
Date: 2023-06-03 15:10:42
Email: 1336299411@qq.com
LastEditors:  
LastEditTime: 2023-06-15 17:44:52
Description: 
version:  
'''
from z3 import *
from mpZ3_beta3_6_2.mp_z3 import *
from mpZ3_beta3_6_2.sv_utils import *
from timeit import timeit

def do_mp():
      # 9x9 matrix of integer variables
      X = [ [ Int("x_%s_%s" % (i+1, j+1)) for j in range(9) ]
            for i in range(9) ]
      # each cell contains a value in {1, ..., 9}
      cells_c = [ And(1 <= X[i][j], X[i][j] <= 9)
                  for i in range(9) for j in range(9) ]
      # each row contains a digit at most once
      rows_c = [ Distinct(X[i]) for i in range(9) ]
      # each column contains a digit at most once
      cols_c = [ Distinct([ X[i][j] for i in range(9) ])
                  for j in range(9) ]
      # each 3x3 square contains a digit at most once
      sq_c = [ Distinct([ X[3*i0 + i][3*j0 + j]
                              for i in range(3) for j in range(3) ])
                  for i0 in range(3) for j0 in range(3) ]
      sudoku_c = cells_c + rows_c + cols_c + sq_c
      # sudoku instance, we use '0' for empty cells
      instance = ((0,0,0,0,9,4,0,3,0),
                  (0,0,0,5,1,0,0,0,7),
                  (0,8,9,0,0,0,0,4,0),
                  (0,0,0,0,0,0,2,0,8),
                  (0,6,0,2,0,1,0,5,0),
                  (1,0,2,0,0,0,0,0,0),
                  (0,7,0,0,0,0,5,2,0),
                  (9,0,0,0,6,5,0,0,0),
                  (0,4,0,9,7,0,0,0,0))

      instance_c = [ If(instance[i][j] == 0,
                        True,
                        X[i][j] == instance[i][j])
                  for i in range(9) for j in range(9) ]
      s = mpZ3Solver(UC.MP_ON)
      s.add(sudoku_c + instance_c)
      if s.check() == sat:
            m = s.model()
            r = [ [ m.evaluate(X[i][j]) for j in range(9) ]
                  for i in range(9) ]
            print_matrix(r)
      else:
            print("failed to solve")

def do_sg():
      # 9x9 matrix of integer variables
      X = [ [ Int("x_%s_%s" % (i+1, j+1)) for j in range(9) ]
            for i in range(9) ]
      # each cell contains a value in {1, ..., 9}
      cells_c = [ And(1 <= X[i][j], X[i][j] <= 9)
                  for i in range(9) for j in range(9) ]
      # each row contains a digit at most once
      rows_c = [ Distinct(X[i]) for i in range(9) ]
      # each column contains a digit at most once
      cols_c = [ Distinct([ X[i][j] for i in range(9) ])
                  for j in range(9) ]
      # each 3x3 square contains a digit at most once
      sq_c = [ Distinct([ X[3*i0 + i][3*j0 + j]
                              for i in range(3) for j in range(3) ])
                  for i0 in range(3) for j0 in range(3) ]
      sudoku_c = cells_c + rows_c + cols_c + sq_c
      # sudoku instance, we use '0' for empty cells
      instance = ((0,0,0,0,9,4,0,3,0),
                  (0,0,0,5,1,0,0,0,7),
                  (0,8,9,0,0,0,0,4,0),
                  (0,0,0,0,0,0,2,0,8),
                  (0,6,0,2,0,1,0,5,0),
                  (1,0,2,0,0,0,0,0,0),
                  (0,7,0,0,0,0,5,2,0),
                  (9,0,0,0,6,5,0,0,0),
                  (0,4,0,9,7,0,0,0,0))

      instance_c = [ If(instance[i][j] == 0,
                        True,
                        X[i][j] == instance[i][j])
                  for i in range(9) for j in range(9) ]
      s = mpZ3Solver(UC.MP_OFF)
      s.add(sudoku_c + instance_c)
      if s.check() == sat:
            m = s.model()
            r = [ [ m.evaluate(X[i][j]) for j in range(9) ]
                  for i in range(9) ]
            print_matrix(r)
      else:
            print("failed to solve")

if __name__ == '__main__':
      mp_time = timeit(do_mp, number=1)
      sg_time = timeit(do_sg, number=1)
      print(f"coust time:\n\tmp: {mp_time:.4f}s\n\tsg :{sg_time:.4f}s")