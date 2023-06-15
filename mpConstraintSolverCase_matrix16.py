'''
Author: Uzio
Date: 2023-06-07 19:16:49
Email: 1336299411@qq.com
LastEditors:  
LastEditTime: 2023-06-15 17:48:32
Description: 
version:  
'''

from z3 import *
from mpZ3_beta3_6_2.mp_z3 import *
from mpZ3_beta3_6_2.sv_utils import *
from timeit import timeit
import random

ORDER = 16
UNIT_ORDER = 4

class Sudoku(object):
      def __init__(self, order:int) -> None:
            assert order > 0
            self.order = order
            
      def Generator(self):
            matrix = [None  * self.order]
            for r in range(self.order):
                  checked = False
                  row = [range(1,self.order + 1)]
                  while not checked:
                        random.shuffle(row)
                        if r == 0:
                              matrix[r] = row
                              checked = True
                        for i in range(r):
                              if matrix[i] is None:
                                    pass
                              
                              
                  
                  
            
      

def do_mp():
      # 9x9 matrix of integer variables
      X = [ [ Int("x_%s_%s" % (i+1, j+1)) for j in range(ORDER) ]
            for i in range(ORDER) ]
      # each cell contains a value in {1, ..., order}
      cells_c = [ And(1 <= X[i][j], X[i][j] <= ORDER)
                  for i in range(ORDER) for j in range(ORDER) ]
      # each row contains a digit at most once
      rows_c = [ Distinct(X[i]) for i in range(ORDER) ]
      # each column contains a digit at most once
      cols_c = [ Distinct([ X[i][j] for i in range(ORDER) ])
                  for j in range(ORDER) ]
      # each orderxorder square contains a digit at most once
      sq_c = [ Distinct([ X[UNIT_ORDER*i0 + i][UNIT_ORDER*j0 + j]
                              for i in range(UNIT_ORDER) for j in range(UNIT_ORDER) ])
                  for i0 in range(UNIT_ORDER) for j0 in range(UNIT_ORDER) ]
      sudoku_c = cells_c + rows_c + cols_c + sq_c
      # sudoku instance, we use '0' for empty cells
     
      instance = ((0, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 16),
                  (0, 6, 0, 0, 1, 0, 0, 0, 0, 14, 0, 0, 4, 0, 0, 15),
                  (7, 10, 0, 0, 0, 0, 16, 0, 1, 0, 0, 3, 0, 0, 0, 0),
                  (13, 0, 0, 0, 0, 0, 0, 11, 0, 6, 8, 12, 0, 0, 0, 0),
                  (0, 0, 4, 3, 0, 0, 0, 0, 0, 11, 12, 0, 0, 0, 16, 0),
                  (0, 0, 0, 0, 2, 0, 9, 0, 0, 0, 0, 14, 10, 0, 12, 0),
                  (0, 11, 0, 13, 3, 0, 0, 16, 0, 0, 0, 4, 0, 0, 0, 0),
                  (9, 0, 0, 14, 0, 0, 12, 0, 0, 0, 5, 8, 0, 0, 0, 0),
                  (3, 0, 0, 0, 0, 1, 6, 9, 0, 13, 0, 0, 0, 0, 0, 0),
                  (8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 15, 0, 9, 10),
                  (0, 0, 14, 0, 12, 16, 0, 0, 7, 1, 0, 0, 0, 0, 0, 0),
                  (12, 0, 0, 10, 0, 0, 0, 14, 0, 0, 11, 6, 0, 0, 0, 0),
                  (0, 3, 5, 0, 9, 0, 0, 0, 0, 8, 0, 0, 0, 0, 15, 0),
                  (0, 0, 6, 0, 0, 0, 0, 0, 11, 0, 15, 7, 13, 0, 0, 0),
                  (0, 13, 9, 7, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 5),
                  (0, 0, 10, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 8, 2, 1))


      instance_c = [ If(instance[i][j] == 0,
                        True,
                        X[i][j] == instance[i][j])
                  for i in range(ORDER) for j in range(ORDER) ]
      s = mpZ3Solver(UC.MP_ON)
      s.add(sudoku_c + instance_c)
      if s.check() == sat:
            m = s.model()
            r = [ [ m.evaluate(X[i][j]) for j in range(ORDER) ]
                  for i in range(ORDER) ]
            print_matrix(r)
      else:
            print("failed to solve")

def do_sg():
      # ORDERxORDER matrix of integer variables
      X = [ [ Int("x_%s_%s" % (i+1, j+1)) for j in range(ORDER) ]
            for i in range(ORDER) ]
      # each cell contains a value in {1, ..., ORDER}
      cells_c = [ And(1 <= X[i][j], X[i][j] <= ORDER)
                  for i in range(ORDER) for j in range(ORDER) ]
      # each row contains a digit at most once
      rows_c = [ Distinct(X[i]) for i in range(ORDER) ]
      # each column contains a digit at most once
      cols_c = [ Distinct([ X[i][j] for i in range(ORDER) ])
                  for j in range(ORDER) ]
      # each 3x3 square contains a digit at most once
      sq_c = [ Distinct([ X[UNIT_ORDER*i0 + i][UNIT_ORDER*j0 + j]
                              for i in range(UNIT_ORDER) for j in range(UNIT_ORDER) ])
                  for i0 in range(UNIT_ORDER) for j0 in range(UNIT_ORDER) ]
      sudoku_c = cells_c + rows_c + cols_c + sq_c
      # sudoku instance, we use '0' for empty cells
      instance = ((0, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 16),
                  (0, 6, 0, 0, 1, 0, 0, 0, 0, 14, 0, 0, 4, 0, 0, 15),
                  (7, 10, 0, 0, 0, 0, 16, 0, 1, 0, 0, 3, 0, 0, 0, 0),
                  (13, 0, 0, 0, 0, 0, 0, 11, 0, 6, 8, 12, 0, 0, 0, 0),
                  (0, 0, 4, 3, 0, 0, 0, 0, 0, 11, 12, 0, 0, 0, 16, 0),
                  (0, 0, 0, 0, 2, 0, 9, 0, 0, 0, 0, 14, 10, 0, 12, 0),
                  (0, 11, 0, 13, 3, 0, 0, 16, 0, 0, 0, 4, 0, 0, 0, 0),
                  (9, 0, 0, 14, 0, 0, 12, 0, 0, 0, 5, 8, 0, 0, 0, 0),
                  (3, 0, 0, 0, 0, 1, 6, 9, 0, 13, 0, 0, 0, 0, 0, 0),
                  (8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 15, 0, 9, 10),
                  (0, 0, 14, 0, 12, 16, 0, 0, 7, 1, 0, 0, 0, 0, 0, 0),
                  (12, 0, 0, 10, 0, 0, 0, 14, 0, 0, 11, 6, 0, 0, 0, 0),
                  (0, 3, 5, 0, 9, 0, 0, 0, 0, 8, 0, 0, 0, 0, 15, 0),
                  (0, 0, 6, 0, 0, 0, 0, 0, 11, 0, 15, 7, 13, 0, 0, 0),
                  (0, 13, 9, 7, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 5),
                  (0, 0, 10, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 8, 2, 1))


      instance_c = [ If(instance[i][j] == 0,
                        True,
                        X[i][j] == instance[i][j])
                  for i in range(ORDER) for j in range(ORDER) ]
      s = mpZ3Solver(UC.MP_OFF)
      s.add(sudoku_c + instance_c)
      if s.check() == sat:
            m = s.model()
            r = [ [ m.evaluate(X[i][j]) for j in range(ORDER) ]
                  for i in range(ORDER) ]
            print_matrix(r)
      else:
            print("failed to solve")
            
            
if __name__ == '__main__':
      mp_time = timeit(do_mp, number=1)
      sg_time = timeit(do_sg, number=1)
      print(f"coust time:\n\tmp: {mp_time:.4f}s\n\tsg :{sg_time:.4f}s")