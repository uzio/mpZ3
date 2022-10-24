'''
Author: Uzio
Date: 2022-04-18 22:56:07
Email: 1336299411@qq.com
LastEditors:  
LastEditTime: 2022-07-13 16:39:58
Description: 解算器/验证器结构设计
version: 2.3-pre
'''
# encoding : utf-8
from multiprocessing import Queue
from multiprocessing.connection import PipeConnection
import os
import sys
import time #TEST
import z3
import operator
import collections
# import multiprocessing as mp
from typing import Any
from loguru import logger

from .sv_utils import SolveUtil#, TObjUtil
from .sv_util_const import UtilConst as UC

# PART 1
class subSolver():
    def __init__(self, utils:SolveUtil=None, *, max=10000):
        assert (utils is not None) , AssertionError('参数缺失')
        self.utils = utils
        self._max = max
    
    def __hash__(self) -> int:
        return hash(tuple(self.utils))
    
    def __eq__(self, __o: object) -> bool:
        return tuple(self.utils._getFlag()) == tuple(self.utils._getFlag())
    
    def __call__(self, *args: Any, pipe:PipeConnection=None, queue:Queue=None, **kwds: Any) -> Any:
        self.utils._setSolve(self._solve(args[0]) if args and isinstance(args[0],int) else self._solve())
        # return self.utils
        try:
            if pipe:
                pipe.send(self.utils)
            if queue:
                queue.put(self.utils)    
            return self.utils
        except Exception as e:
            logger.info(f"进程间通信失败-{e}")
        
        
    def _solve(self, max:int=None):
        remain = max if max is not None else self._max #NOTE 默认最多求解次数
        _id = self.utils._getFlag().id #TODO* FlagUtil对象的作用
        
        _solveSet = collections.defaultdict(list) # 创建默认元素为空列表的字典，便于更新解集
        
        constraints = self.utils(op_name=UC.OP_S)
        
        Solver = z3.Solver()
        try:
            Solver.add(constraints) #>>添加约束分集
        except Exception as e:
            logger.error(f"解算器约束添加失败-{e}")
        if(Solver.check() != z3.sat):
            return { } #NOTE 无解，返回空集 -> #TODO 出现空集，终止所有同分支解算器
        else:
            while(Solver.check() == z3.sat and remain>0):
                remain -= 1
                exc = [ ] # 额外约束
                
                _model = Solver.model()
                for _expr in _model:
                    _var = _expr()
                    _val = _model.eval(_var, model_completion=True)
                    exc.append(z3.Not(_var == _val)) #* 保存本轮建模的解(集)为额外约束
                    _solveSet[_id].append((_var ==_val).sexpr())
                    
                Solver.add(exc)
                solveSet = {_id: tuple(_solveSet[_id])} #FIX 多解情况的分组方案不准确
            return solveSet
# END 1

# PART 2
class subValidor():
    def __init__(self, o_utils:SolveUtil=None, ex_utils:SolveUtil=None, only_check=False):
        assert (o_utils is not None) , AssertionError('参数缺失')
        if only_check: #* 单独用作多进程验证
            self.o_utils = o_utils
            self.ex_utils = None
            self.only = True
        else:    
            self.o_utils = o_utils #* 加载相同约束单元的验证器和解算器可视为代表总集上的同一作用域
            self.ex_utils = ex_utils
            self.only = False
        
    def __hash__(self) -> int:
        return hash(tuple(self.o_utils))
    
    def __eq__(self, __o: object) -> bool:
        return tuple(self.o_utils._getStatus()) == tuple(self.o_utils._getStatus())
    
    def __call__(self,case=None, *args: Any, pipe:PipeConnection=None, queue:Queue=None, **kwds: Any) -> Any:
        # return self._verify()
        if self.only:
            vfresult = self._check()
        else:
            vfresult = self._verify()
        # logger.debug('gone')
        try:
            if pipe:
                pipe.send(vfresult)
            if queue:
                queue.put(vfresult)    
            return vfresult
        except Exception as e:
            logger.info(f"进程间通信失败-{e}")
        
    
    def setExtra(self, utils):
        self.ex_utils = utils
    
    def _check(self):
        Validator = z3.Solver()
        try:
            Validator.add(self.o_utils(op_name=UC.OP_V))
        except Exception as e:
            logger.error(f"验证器约束添加失败-{e}")
        if Validator.check() == z3.sat:
            return True
        else:
            return False
    
    def _verify(self):
        _id = self.ex_utils._getFlag().id
        
        r = []
        
        constraints = self.o_utils(op_name=UC.OP_S)
        
        Validator = z3.Solver()
        try:
            Validator.add(constraints) #>> 添加约束单元
        except Exception as e:
            logger.error(f"验证器约束添加失败-{e}")
        # _cases = self.ex_utils(op_name=UC.OP_V)
        _cases = (self.ex_utils(op_name=UC.OP_V),) #BUG 找到TypeError的原因
        for _case in _cases:
            Validator.push()
            Validator.add(_case)
            if Validator.check() == z3.sat:
                r.append(True)
            else:
                r.append(False)
            Validator.pop()
        # logger.debug(f">>>  {_id}:{r}")
        return {_id:tuple(r)} #TODO* 设计验证器返回结果的规范方案
# END 2            
            
# if __name__ == '__main__':
    # x = z3.Int('x')
    # y = z3.Bool('y')
    # z = z3.String('z')
    
    # #PART step 1 变量对象的属性映射为字典 #
    # names = []
    # funcs = []
    # for obj in [x,y,z]:
    #     names.append(obj.sexpr())
    #     if isinstance(obj,z3.ArithRef):
    #         _z3Func = 'Real' if obj.is_real() else 'Int'
    #     elif isinstance(obj,z3.BoolRef):
    #         _z3Func = 'Bool'
    #     elif isinstance(obj,z3.SeqRef):
    #         _z3Func = 'String'
    #     else:
    #         _z3Func = 'unknown' #TODO 更多变量类型封装
    #     funcs.append(_z3Func)
    
    # varset_dict = dict(zip(names,funcs))
    
    # utils = SolveUtil()
    # utils._setVars(varset_dict) #>> 封装类实例拿到变量信息
    # #END
    # #PART 2 
    # cons = z3.And(x>=15,x>-10,z3.Or(x!=2, z3.And(x!=3,x!=1)), z3.Not(x==0), y==True, y!=False, z=='a').sexpr() #TODO Bool对象y，设置如 y = x+1 类型的表达式时，替换方案未实现
    # others = (z != '0').sexpr() #TEST 尝试添加其他约束单元作为识别参数
    # utils._setCons(cons) #>> 封装类实例拿到约束信息
    # utils._setFlag(others)
    # # print(utils())
    # #END
    
    # #TEST 效率比较
    # ##TEST 1
    # sol = subSolver(utils)
    
    # s = time.time()
    # for _ in range(1):
    #     utils=sol(10)
    # e = time.time()
    
    # cs = time.time()
    # try:
    #     pool = mp.Pool(processes=mp.cpu_count())
    #     pool.map(sol,[10]*1)
    # except RuntimeError:
    #     print("RuntimeError")
    # ce = time.time()
    # print(f'S ->\n\tFor-Loop > Time Cost: {e-s}\n\tMP\t > Time Cost: {ce-cs}')
    
    # ##TEST 2
    # ver = subValidor(utils,utils)
    # # logger.info(ver())#TEST 查看验证器返回结果
    # s2 = time.time()
    # for _ in range(10):
    #     ver()
    # e2 = time.time()
    
    # cs2 = time.time()
    # try:
    #     pool = mp.Pool(processes=mp.cpu_count())
    #     pool.map(ver,[]*10)
    # except RuntimeError:
    #     print("RuntimeError")
    # ce2 = time.time()
    # print(f'V ->\n\tFor-Loop > Time Cost: {e2-s2}\n\tMP\t > Time Cost: {ce2-cs2}')