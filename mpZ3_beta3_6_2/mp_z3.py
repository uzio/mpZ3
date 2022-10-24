'''
Author: Uzio
Date: 2022-04-20 15:30:21
Email: 1336299411@qq.com
LastEditors:  
LastEditTime: 2022-10-24 09:42:27
Description: API-多进程加速方案的高级接口封装
version: 3.6.2-pre
'''
import re
import traceback
from loguru import logger
from typing import List, Union
from .hs_convert import hex_to_str
# from .lsc_cache import LSCCache
from .sv_utils import SolveUtil, TObjUtil
from .sv import *
from binascii import a2b_hex, b2a_hex
import multiprocessing as mp

class mpZ3Solver(z3.Solver):
    def __init__(self, state=UC.MP_ON, *, solver=None, ctx=None, logFile=None):
        super().__init__(solver, ctx, logFile)
        self._trigger = None
        try:
            if state == UC.MP_ON:  #TODO 多进程任务
                logger.info("多进程模式")
                self._trigger = True

            elif state == UC.MP_OFF:
                logger.info("单进程模式")
                self._trigger = False
            else:
                raise InterruptedError("未知模式,放弃加速方案")
            
        except Exception as e:
                logger.warning(e)
                self._trigger = False
    
    def solve(self,*args, **kwargs):
        if self._trigger:
            mpc = mpController(self)
            result = mpc(*args) #! 多进程
            return result
            # try:
            #     mpc(*args) #! 多进程
            # except Exception as e:
            #     logger.error(e)
            #     logger.warning('切换-单进程模式')
            #     self._trigger = False
        
        if not self._trigger: #TODO 单进程求解的功能补全
            if self.check() == z3.sat:
                return self.model()
            else:
                return #TODO
            
    # def check(self, expr, constraints, *args, **kwargs):
    #     mpc = mpController(self)
    #     mpc._setVarObj(expr.arg(0) if expr.num_args() > 0 else expr)
    #     o_utils = mpc._divide()
    #     LValidors = mpc._build(utils=o_utils)
    #     for ver in self.LValidors:
    #         ver.setExtra()
    #     judges = mpc._dispatch(LValidors)
    #     if all(all((judge.values()) for judge in judges) if judges is not None else {}):
    #         return z3.sat
    #     elif not all(all((judge.values()) for judge in judges) if judges is not None else {}):
    #         return z3.unsat
    #     else:
    #         return z3.unknown
    #     return z3.sat
               

class mpController():
    def __init__(self, task:mpZ3Solver) -> None:
        self.totalSet =[_.sexpr() for _ in task.assertions()] #* 获取约束全集
        
        #TODO 分别建立存放解算单元、解算器/验证器子进程的缓存
    
    def __call__(self, *args: Any, **kwds: Any) -> Any: #>> 方法调用顺序
        self._setVarObj(*args)
        o_utils = self._divide() 
        self.LSolvers, self.LValidors = self._build(utils=o_utils) # 创建列表保存所有解算器/验证器对象
        solves = self._dispatch(self.LSolvers)
        # if solves: #! 每个解算器的返回结果均需要经过全体验证器的验证 -> 排除本身对应的验证器
        #     #TODO* 如果条件包含等式,则跳过验证步骤
        #     for s in solves:
        #         for ver in self.LValidors:
        #             ver.setExtra(s) 
                    
        #         judges = self._dispatch(self.LValidors)
        #         _j = all(all(judge.values()) for judge in judges)#TODO 获取判断
        # else:
        #     logger.debug(f"pass")
        #TODO* 删除失效解 
        res = [solves[i](TObjUtil(), op_name=UC.OP_V) for i in range(len(solves))]
        # print(res)
        # logger.debug(res)
        #排序
        _r = []
        for _ in res:
            # assert isinstance(_, list)
            if isinstance(_, list):
                _r.extend(_)
            elif isinstance(_, bool):
                continue
            else:
                _r.extend(list(_))
            
        res = [_.sexpr() for _ in _r]
        #TODO* 筛选位向量类型进行排序后输出
        res.sort(key=lambda I:int(re.findall('\d+',I)[0])) #*排序
        # ir = (int(res[i].strip('(').strip(')').split(' ')[2].replace('#x','0x'), 16) for i in range(len(res)))
        # pr = ''.join(chr(s)for s in (r if r <=255 else 32 for r in ir)).replace(' ','')
        # print(f"多进程联合求解>>{pr}")
        # logger.debug(''.join(hex_to_str(res[i].strip('(').strip(')').split(' ')[2].replace('#x','')) for i in range(len(res))))#TEST 顺序
        #// logger.debug(''.join(hex_to_str(_r[i].sexpr().strip('(').strip(')').split(' ')[2].replace('#x','')) for i in range(len(_r))))#TEST 顺序
        return res
        # return solves       
    
    #PART 1 Get variable object - 获取变量对象
    def _setVarObj(self, *args):
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
                _z3Func = ('BitVec', obj.size()) #FIX 位向量的大小加入映射
            else:
                raise NameError(f"变量对象映射规则缺失") #TODO 更多变量类型映射封装
            
            funcs.append(_z3Func)
        
        self.varSetDict = dict(zip(names,funcs))
        # logger.debug(f">>符号变量特征:{self.varSetDict}")#TEST 
        
    #PART 2 Divide total set into cells - 将总约束集合分解为约束单元
    @staticmethod
    def _groups(total, per_len):

        '''
        name: groups
        msg: 将列表按定长分割
        return {分割后的列表组}
        '''
        _group = zip(*(iter(total),) *per_len) 
        new_list = [list(i) for i in _group]
        count = len(total) % per_len #! 取整
        new_list.append(total[-count:]) if count != 0 else new_list
        return new_list
    
    # global debug_cons#TEST 
    # debug_cons = {}#TEST 
    def _divide(self, granularity:int=None): #// TODO 分解粒度默认参数待优化
        '''
        name: divide
        msg: 将总约束集合分解为约束单元，并完成解算单元的封装
        param {granularity:int -> 约束全集的分解粒度，影响解算单元中约束单元的最大值}
        return {解算单元(约束)列表}
        ''' 
        if granularity is None:
            import math
            param = 2 #? 约定参数
            granularity = math.ceil((len(self.totalSet))/(mp.cpu_count())) * param #? 默认以约束全集元素数量/逻辑处理器数量(向上取整)×约定参数 为参数进行分组
            del math
        
        # #TEST 测试解算单元功能
        # util = SolveUtil(self.varSetDict)
        # util._setCons(self.totalSet[0])
        # _temp = TObjUtil()
        # logger.info(util._getCons(_temp,util._getVars(_temp)))
        # ##TEST END
        utils = []#? 缓存 -> 约束条件不需要缓存，保存解值需要
        #// granularity = len(self.totalSet) if granularity > len(self.totalSet) else granularity
        _set = ['\n'.join(_) for _ in self._groups(self.totalSet, granularity)]
        # logger.debug(f"ori:{self.totalSet[1]}\ndivide:{_set}")
        # for _ in range(granularity):
        for _s in _set:
            util = SolveUtil(self.varSetDict) #! 为每个约束单元创建解算单元
            #// util._setCons(self.totalSet[_]) #! 将约束单元加载到解算单元
            util._setCons(_s) #! 将约束单元加载到解算单元
            # global debug_cons #TEST 
            # debug_cons.update({id(util):_s})
            # util._setFlag(self.totalSet[_:]) #TODO 设置解算单元的标识
            utils.append(util)
        return utils
    # global debug_cons
    #TODO 
    #PART 3 创建解算器/验证器对象
    def _build(self, utils):
        '''
        name: build
        msg: 创建解算器/验证器对象
        param {*}
        return {解算器/验证器列表}
        '''
        try:
            solvers = []
            validors = []
            for cons in utils:
                solvers.append(subSolver(utils=cons, max=1))
                validors.append(subValidor(o_utils=cons)) #* 每个解算器对应一个同约束条件的验证器
            return solvers, validors
        except Exception as e:
            logger.error(f"解算器/验证器创建失败-{e}")
            return 
            
    #PART 4 创建进程队列
    @staticmethod
    def _create(obj:Union[subSolver,subValidor], pargs:tuple, pkwargs:dict):
        '''
        name: create
        msg: 创建进程
        return {*}
        '''
        process = mp.Process(target=obj, args=pargs, kwargs=pkwargs) #TODO 进程命名
        process.daemon = False
        return process
    
    #PART 5 进程调度
    def _dispatch(self, subObjs:List[Union[subSolver,subValidor]]): #TODO* 
        '''
        name: dispatch
        msg: 进程调度
        return {*}
        '''
        # Pipe = []
        Pranks = []
        manager = mp.Manager()
        _Queue = manager.Queue(maxsize=500) # 队列长度参数
        try:
            for obj in subObjs:
                # logger.debug(obj)
                if isinstance(obj, subSolver):
                # mpipe, spipe = mp.Pipe()
                # p = self._create(obj=obj, pargs=(10,), pkwargs={'pipe':spipe})
                # Pipe.append((mpipe, spipe))
                    p = self._create(obj=obj, pargs=(10,), pkwargs={'queue':_Queue})
                    # logger.warning(f"进程信息：{p.name} ->对应约束对象：{debug_cons[id(obj.utils)]}")
                    Pranks.append(p)
                elif isinstance(obj, subValidor):
                    p = self._create(obj=obj,pargs=(None,), pkwargs={'queue':_Queue})
                    Pranks.append(p)
                else:
                    raise TypeError("创建进程的目标对象不符合要求")
        except Exception as e:
            logger.error(f"进程创建失败-{e}")
            return
        try: #* 启动所有进程
            # logger.debug(Queue)
            # logger.debug(Pipe)
            _running = []
            for p in Pranks:
                _running.append(p)
                
                p.start()
                p.join()
                # p.join(timeout=10)
                _running = self._liveCheck(_running, max=mp.cpu_count())
                
            # list(map(mp.Process.start,Pranks)) #// DEBUG 无法接收到子进程反馈 -> python3的map函数返回迭代器，导致没有直接运行进程
            # list(map(mp.Process.join, Pranks))
            
            # print(flag)
        
            # logger.debug(Pipe[0][1].recv())
            # solves = []
            # logger.debug("运行结算")#// DEBUG 
            results = [_Queue.get() for p in Pranks] #! 子进程返回结果集合
            # logger.debug(f"结果>>>{results}")#// DEBUG 
            return results
            # solves.append(spipe.recv())
            # logger.debug(solves)
        except Exception as e:
            logger.error(f"进程运行失败-{e}")
            return None
        # finally:
            # mpipe.close()
            # spipe.close()
            # for _ in Pipe:
            #     _[0].close()
            #     _[1].close()
            # logger.debug(f"done.")
    @staticmethod
    def _liveCheck(plist=None, max=None):
        '''
        name: liveCheck
        msg: 进程存活检测
        return {*}
        '''
        if plist is None:
            return 
        if max is None or max > mp.cpu_count():
            max = mp.cpu_count()
        while len(plist) >= max:
            plist = [p for p in plist if p.is_alive()]
        return plist
            
        
    #PART 6 结果处理
    #TODO 将解算单元存入缓存-> 缓存采用生存检查机制，仅保存有效单元

# if __name__ == '__main__':
#     # def do():
#     #     x = z3.Int('x')
#     #     y = z3.Bool('y')
#     #     z = z3.String('z')
        
#     #     mps = mpZ3Solver(UC.MP_ON)
#     #     mps.add(z3.And(x>=15,x>-10,z3.Or(x!=2, z3.And(x!=3,x!=1)), z3.Not(x==0), y==True), y!=False, z=='a')
#     #     mps.solve(x,y,z)
#     # t = timeit(stmt='do()', setup='from __main__ import do', number=1)
#     # print(f"time count>{t:.4f}s")
#     # exit()
#     from timeit import timeit
#     from hs_convert import str_to_hex, hex_to_str
#     string = "Ae86!!FG232di223a5dh56768686879898797979796967898787006" #* 目标约束
#     h_str = str_to_hex(string)#* 转换成16进制
#     # print(h_str) #TEST 
#     r_result = bytearray(a2b_hex(h_str.replace(' ', ''))) #* 转换成二进制数组
#     # for i in range(len(r_result) // 2): # 翻转
#     #     c = r_result[i]
#     #     r_result[i] = r_result[len(r_result) - i - 1]
#     #     r_result[len(r_result) - i - 1] = c
#     x = [z3.BitVec(f'x{i}', 32) for i in range(len(r_result))] #*针对该数组创建位向量数组
        
#     def do_mp():
#         mps = mpZ3Solver(UC.MP_ON)
        
#         # st = time.time()#*计时开始
#         for i in range(len(r_result)):
#             mps.add(x[i] == r_result[i])
        
#         mps.solve(*x)
#         # ed = time.time() #*计时结束
#         # print(f"多进程耗时：{ed-st:.4f}s")
#     mp_time = timeit(do_mp,number=1)
#     print(f"多进程耗时: {mp_time:.4f}s")
#     def do_sg():
#         single_Sov = z3.Solver()
#         # st2 = time.time()#*计时开始
#         for i in range(len(r_result)):
#             single_Sov.add(x[i] == r_result[i])
#         if single_Sov.check() == z3.sat:
#             model = single_Sov.model()
#             flag = ''
#             for i in range(len(r_result)):
#                 try:
#                     flag += chr(model[x[i]].as_long().real)
#                 except Exception as err:
#                     flag += ' '
#             print([flag])
#         else:
#             print('???')
#         # ed2 = time.time() #*计时结束
#         # print(f"原耗时：{ed2-st2:.4f}s")
#     sg_time = timeit(do_sg,number=1)
#     print(f"单进程z3等价处理耗时: {sg_time:.4f}s")
#     # #PART step 1 变量对象的属性映射为字典 #
#     # names = []
#     # funcs = []
#     # for obj in [x,y,z]:
#     #     names.append(obj.sexpr())
#     #     if isinstance(obj,z3.ArithRef):
#     #         _z3Func = 'Real' if obj.is_real() else 'Int'
#     #     elif isinstance(obj,z3.BoolRef):
#     #         _z3Func = 'Bool'
#     #     elif isinstance(obj,z3.SeqRef):
#     #         _z3Func = 'String'
#     #     else:
#     #         _z3Func = 'unknown' #TODO 更多变量类型封装
#     #     funcs.append(_z3Func)
    
#     # varset_dict = dict(zip(names,funcs))
    
#     # utils = SolveUtil() #>>
#     # utils._setVars(varset_dict) #>> 封装类实例拿到变量信息
#     # #END
#     # #PART 2 
#     # cons = z3.And(x>=15,x>-10,z3.Or(x!=2, z3.And(x!=3,x!=1)), z3.Not(x==0), y==True, y!=False, z=='a').sexpr() #TODO Bool对象y，设置如 y = x+1 类型的表达式时，替换方案未实现
#     # others = (z != '0').sexpr() #TEST 尝试添加其他约束单元作为识别参数
#     # utils._setCons(cons) #>> 封装类实例拿到约束信息
#     # utils._setFlag(others)
#     # #END
    
#     # #TEST 效率比较
#     # ##TEST 1
#     # sol = subSolver(utils)
    
#     # s = time.time()
#     # for _ in range(1):
#     #     utils=sol(10)
#     # e = time.time()
    
#     # cs = time.time()
#     # try:
#     #     pool = mp.Pool(processes=mp.cpu_count())
#     #     pool.map(sol,[10]*1)
#     # except RuntimeError:
#     #     print("RuntimeError")
#     # ce = time.time()
#     # print(f'S ->\n\tFor-Loop > Time Cost: {e-s}\n\tMP\t > Time Cost: {ce-cs}')
    
#     # ##TEST 2
#     # ver = subValidor(utils,utils)
    
#     # s2 = time.time()
#     # for _ in range(10):
#     #     ver()
#     # e2 = time.time()
    
#     # cs2 = time.time()
#     # try:
#     #     pool = mp.Pool(processes=mp.cpu_count())
#     #     pool.map(ver,[]*10)
#     # except RuntimeError:
#     #     print("RuntimeError")
#     # ce2 = time.time()
#     # print(f'V ->\n\tFor-Loop > Time Cost: {e2-s2}\n\tMP\t > Time Cost: {ce2-cs2}')