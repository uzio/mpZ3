'''
Author: Uzio
Date: 2022-07-10 10:17:34
Email: 1336299411@qq.com
LastEditors:  
LastEditTime: 2022-08-17 18:03:41
Description: 
version: 1.0
'''
from asyncio import constants
import sys
import z3
import operator
import multiprocessing as mp
from timeit import timeit
from loguru import logger as l
from mpZ3_beta3_6_2.mp_z3 import mpZ3Solver, mpController
# from mpZ3_beta3_6.sv_util_const import UtilConst as UC
from mpZ3_beta3_6_2.sv_utils import *

def setVarObj(*args):
        '''
        name: setVarObj
        msg: 将z3.*类型的变量对象的信息映射到字典
        param {*args:z3.* -> 变量对象}
        return {*}
        '''        
        assert args, logger.warning(AssertionError("变量对象未获取"))
        names = []
        funcs = []
        for obj in args:
            names.append(obj.sexpr())
            if isinstance(obj,z3.ArithRef):
                _z3Func = 'Real' if obj.is_real() else 'Int'
            elif isinstance(obj,z3.BoolRef):
                _z3Func = 'Bool'
            elif isinstance(obj,z3.SeqRef):
                _z3Func = 'String'
            elif isinstance(obj,z3.BitVecRef):
                _z3Func = ('BitVec', obj.size()) 
            else:
                raise NameError(f"变量对象映射规则缺失") 
            
            funcs.append(_z3Func)
        
        varSetDict = dict(zip(names,funcs))
        return varSetDict

def mpBinarySearch(signed, region:tuple, util:SolveUtil, *args, queue=None ,**kwargs):
    GT = operator.gt if signed else z3.UGT
    GE = operator.ge if signed else z3.UGE
    LT = operator.lt if signed else z3.ULT
    LE = operator.le if signed else z3.ULE
    
    lo, hi = region
    
    solver = z3.Solver()
    _temp = TObjUtil()
    #* 约束反序列化
    name = util._getVars(_temp)
    expr = _temp.__dict__[name[0]]
    # logger.debug(type(expr))
    constraints = [util(op_name=UC.OP_S)]
    # solver.add(constraints)
    # solver.push()
    new_constraints = []
    ret = None
    
    if solver.check(constraints + [z3.And(GE(expr, lo), LE(expr, hi))]) != z3.sat:
        # logger.warning(f"pass lo:{lo}") if lo == 0 else logger.debug('PASS')
        ret = None
        queue.put(ret)
        sys.exit(0)
    elif solver.check(constraints + [GT(expr, hi)]) == z3.sat:
        # logger.warning(f"pass hi:{hi}")
        ret = None
        queue.put(ret)
        sys.exit(0)
    else:
        while hi-lo > 1:
            # logger.debug(f"do {region}")
            middle = (lo + hi)//2
            new_constraints.append(z3.And(GT(expr, middle), LE(expr, hi)))
            # logger.debug(new_constraints)
        
            # logger.debug(f"lo:{lo} hi:{hi} middle:{middle}")
            if solver.check(constraints + new_constraints) == z3.sat: #TODO* 重写mpZ3的验证器单独调用方法， 完成约束还原和可满足性检查
                lo = middle
            else:
                hi = middle
                new_constraints.pop()
                
        if hi == lo:
            ret = hi
        else:
            if solver.check(constraints + [expr == hi]) == z3.sat:
                ret = hi
            elif solver.check(constraints + [expr == lo]) == z3.sat:
                ret = lo
            else:
                ret = None
            
    # logger.debug(ret)
    queue.put(ret)
    # return ret

def max(expr, constraints=(), signed=False, solver=None): #* 修改
    if signed:
        if expr.size() > 64:
            mp_ON = True
            cut = (expr.size()-1) // 64
            # regions_lo = [-2**(64*(n))-1 if n != cut else -2**(expr.size()-1) for n in range(cut+1)]
            # regions_hi = [2**(64*(n))-1 if n != cut else 2**(expr.size()-1)-1 for n in range(cut+1)]
            regions = [(-2**(64*(n))-1 if n != cut else -2**(expr.size()-1),2**(64*(n))-1 if n != cut else 2**(expr.size()-1)-1) for n in range(1,(cut+1))]  # 去除低价值区间[-2, 0]
            #TODO* 将正负区间分别处理
            #! 逆序，优先判断表达式是否在大区间内可满足
            regions.reverse()
            # print(f"size:{64*(cut)}\n{regions}")
            # # print(f"size:{expr.size()-1}\nlo:{-2**(expr.size()-1)}\nhi:{2**(expr.size()-1)-1}")
            # exit()
            # re_expr = expr.__repr__().split(' ')[0] # 获取表达式对应的变量名 #TODO 当前仅单变量表达式，后续可以利用正则优化
        else:
            mp_ON = False
            lo = -2**(expr.size()-1)
            hi = 2**(expr.size()-1)-1
    else:
        if expr.size() > 64:
            mp_ON = True
            cut = expr.size() // 64
            modzero = (expr.size() % 64) == 0 
            if modzero:
                regions = [(2**(64*(n-1)), 2**(64*(n))-1) if n > 1 else (0,2**64-1) for n in range(1,(cut+1))]
            else:
                regions = [(2**(64*(n-1)), 2**(64*(n))-1) if n > 1 else (0,2**64-1) for n in range(1,(cut))] + [(2**(64*(cut)), 2**(expr.size())-1)] #! 处理非整数倍的区间
            # print(f"size:{64*(cut)}\n{regions}")
            # print(f"size:{expr.size()}\nlo:{0}\nhi:{2**expr.size()-1}")
            # exit()
            # re_expr = expr.__repr__().split(' ')[0]
            # re_expr = expr.arg(0) if expr.num_args() > 0 else expr #TODO 当前仅单变量表达式
        else:
            mp_ON = False
            lo = 0
            hi = 2**expr.size()-1

    
    new_constraints = []
    
    GT = operator.gt if signed else z3.UGT
    LE = operator.le if signed else z3.ULE
    
    #TODO 多进程验证表达式是否在区间内可满足 -> 按区间分组，将分别创建检查进程
    # 多进程查找最大值
    if mp_ON:
        # l.warning(re_expr)
        _set = setVarObj(expr)
        util = SolveUtil()
        util._setVars(_set)
        # _v = util._getVars(TObjUtil())
        util._setCons(constraints.sexpr())
        # _c = util(op_name=UC.OP_S)
        # l.warning(_c)
        # ret = mpBinarySearch(signed=signed, region=regions[0], util=util) #TODO 改写为多进程
        import multiprocessing as mp
        manager = mp.Manager()
        _Queue = manager.Queue()
        
        pl = [mp.Process(target=mpBinarySearch, args=(signed, region, util), kwargs={'queue':_Queue}) for region in regions]
        list(map(mp.Process.start, pl))
        list(map(mp.Process.join, pl))
        
        _Qresults = list(filter(None, (_Queue.get() for p in pl)))
        # logger.debug(f">>\n{_Qresults}\n")
        ret = sorted(_Qresults)[-1] if _Qresults else 0 #* 获取最大值
        # logger.debug(ret)
        
    else:
        while hi-lo > 1:
            middle = (lo + hi)//2
            new_constraints.append(z3.And(GT(expr, middle), LE(expr, hi)))

            # l.debug("Doing a check! (max)")
            
            if solver.check(*(constraints + new_constraints)) == z3.sat:
                # l.debug("... still sat")
                lo = middle
            else:
                # l.debug("... now unsat")
                hi = middle
                new_constraints.pop()
            # l.debug("          now: %d %d %d %d"%(hi, middle, lo, hi-lo))
                
        ret = None
        if hi == lo:
            ret = hi
        else:
            # l.debug("Doing a check! (max)")
            if solver.check(*(constraints + [expr == hi])) == z3.sat:
                ret = hi
            else:
                ret = lo

    return ret

def ori_max(expr, constraints=(), signed=False, solver=None): #* 原生
    if signed:
        lo = -2**(expr.size()-1)
        hi = 2**(expr.size()-1)-1
    else:
        lo = 0
        hi = 2**expr.size()-1
    
    new_constraints = []
    
    GT = operator.gt if signed else z3.UGT
    LE = operator.le if signed else z3.ULE
    while hi-lo > 1:
        middle = (lo + hi)//2
        new_constraints.append(z3.And(GT(expr, middle), LE(expr, hi)))

        # l.debug("Doing a check! (max)")
        
        if solver.check(*(constraints + new_constraints)) == z3.sat:
            # l.debug("... still sat")
            lo = middle
        else:
            # l.debug("... now unsat")
            hi = middle
            new_constraints.pop()
        # l.debug("          now: %d %d %d %d"%(hi, middle, lo, hi-lo))
                
    ret = None
    if hi == lo:
        ret = hi
    else:
        # l.debug("Doing a check! (max)")
        if solver.check(*(constraints + [expr == hi])) == z3.sat:
            ret = hi
        else:
            ret = lo

    return ret

if __name__ == '__main__':
    x = z3.BitVec('x', 655)
    _s = z3.Solver()
    # _c = z3.And(x > 0, x <= (2**10), x < (2*32), x < (2*64), x <=(2**1), x< (2**2), x< (2**3), x <=(2**5))#? ***约束设置
    
    _c = z3.And(x > 0, x <= (2**111)) #! 初始输入
    # _x = x + 0xff
    # print(f"{z3.is_const(_x)}")
    # print(f"{z3.is_const( x)}")
    # exit()
    def do_ori():
        r = ori_max(x, [_c], False, _s)
        print(f"原生>\t{r}")
    
    def do():
        r = max(x, _c, False, _s) #FIXME 2.耗时不稳定  #DEBUG 1.当最大值是超过2**64的无符号数时，无法得出正确结果 > 子进程结果获取方法不正确，已修正;  
        print(f"修改>\t{r}")
    
    print(f"time count: \n\t原生耗时: {timeit(do_ori, number=1):.4f}s.\n\t修改耗时: {timeit(do, number=1):.4f}s.")
    