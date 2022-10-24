'''
Author: Uzio
Date: 2022-03-26 16:06:25
Email: 1336299411@qq.com
LastEditors:  
LastEditTime: 2022-09-03 16:16:37
Description: 进程间数据交换单元结构设计
version: 2.2
'''
# encoding : utf-8
import os
import re
import sys
import time
import z3
import operator
from loguru import logger
from typing import Any

from .sv_util_const import UtilConst as UC

class TObjUtil :
    '''
    转运类，寄存重建的对象
    '''
    def __delattr__(self, __name: str) -> None:
        logger.debug(f' {__name} 变量已删除')
        super().__delattr__(__name)

class FlagUtil :
    '''
    标识类, 保存数据封装类的约束补集, 提供不同封装类实例间的识别功能, 以及向主进程提交补集
    '''
    def __init__(self, complement=None) -> None:
        self.complement = complement
        self.id = id(self) #TODO* 完善id的生成
    
    #TODO* 定义比较方法

class SolveUtil :
    '''
    数据封装类, 封装属性构建解算单元，用于进程间传递
    通过字符组合替换的方式实现z3数据类型的信息保存和重建还原
    '''
    def __init__(self, varSet:dict=None, *, __constraints:list=None, __flag:FlagUtil=None, __surviving=True, **kwargs) -> None: #TODO 识别ID的组构，补集属性拓展功能：标识覆盖
        self.__varSet = varSet #* 变量参数     
        self.__constraints:list = __constraints #* 约束单元
        self.__solves:dict = None #* 解
        #* Flags for Verifying
        self.__flag = FlagUtil() #? 存储id和约束补集等信息的类
        self.__surviving = __surviving #? 解算单元活性
        
        op_dict = {
            '>':'operator.gt',
            '>=':'operator.ge',
            '<':'operator.lt',
            '<=':'operator.le',
            '=':'operator.eq',
            '!=':'operator.ne',
            '+':'operator.add',
            '-':'operator.sub',
            '*':'operator.mul',
            '/':'operator.truediv',
            '//':'operator.ifloordiv',
        }
        
        z3_dict = {
            'ite':'z3.If',
            'and':'z3.And',
            'or':'z3.Or',
            'not': 'z3.Not',
            'distinct': 'z3.Distinct',
            'bvuge': 'z3.UGE',
            'bvugt': 'z3.UGT',
            'bvule': 'z3.ULE',
            'bvult': 'z3.ULT',
            'bvashr':'z3.LShR',
            'bvadd':'operator.add',
            'bvxor':'operator.xor',
            'bvsgt': 'operator.gt',
            'bvsge': 'operator.ge',
            'bvslt': 'operator.lt',
            'bvsle': 'operator.le',
        }
        
        self.__func_dict = {**op_dict,**z3_dict} #NOTE 还原操作参数字典 #TODO 未支持的转换操作参数待完善
    
    def __call__(self, tobj=None, *, op_name=None, **kwds:Any) -> Any: #>> MAIN CALL
        try:
            _tobj = tobj if tobj and isinstance(tobj,TObjUtil) else TObjUtil()
            _vars = self._getVars(_tobj)
            assert _vars is not None, AssertionError("无有效变量对象")
            if op_name == UC.OP_S:
                return self._getCons(_tobj, _vars)
            elif op_name == UC.OP_V:
                return self._getSolve(_tobj,_vars)
            else:
                logger.warning("未知操作请求")
                
        except Exception as e:
            logger.error(f"约束重建失败-{e}")
            raise
        finally:
            self._del_other(_tobj) #TODO 是否需要立即释放临时转运对象？ 或设计回收方案
    
    #PART 1 VarSet
    def _setVars(self, set:dict):
        self.__varSet = set
    
    def _getVars(self,other): #>> Core Method
        assert (self.__varSet is not None), AssertionError('空变量对象')
        varObj = [ ]
        
        for _name,_func in self.__varSet.items():
            assert _func != 'unknown', AssertionError('无法还原的变量对象')
            try:
                if isinstance(_func, tuple):
                    # # if _name == '(bvadd reg_1c_3_32 #xffffffec)': #? 应急处理
                    #     setattr(other, 'reg_1c_3_32', z3.__dict__[_func[0]](_name, _func[1]))
                        
                    setattr(other, _name, z3.__dict__[_func[0]](_name, _func[1])) #! 重建双参数z3变量对象
                else:
                    setattr(other, _name, z3.__dict__[_func](_name)) #! 重建z3变量对象
            except KeyError as k:
                logger.error(f"z3无对应方法-KeyError:{k}")
            except Exception as e:
                logger.error(f"z3对象重建失败-{e}")
            varObj.append(_name)
        return varObj
    #END    
    
    #PART 2 Constraints
    def _setCons(self, cons:str):
        '''字符约束按最外层指令封装分组'''
        self.__constraints = re.split('\n',cons)
        # logger.debug(self.__constraints)#TEST 
        # exit()
    
    def _getCons(self, other, varname:list): #>> Core Method 字符化约束单元的还原重建
        assert (self.__constraints is not None), AssertionError('空约束')
        cons = self.__constraints
        l_code = []
        f_no_1st = False
        
        # logger.debug(cons)
        for _cons in cons:
            _cons = _cons.strip()
            _cons = re.sub(r'(-)\s(\d)', self.__pattern_del_bks_sub, _cons) #* 负数规范
            _rp_f = [_ for _ in self.__func_dict.keys()]
            for _func in _rp_f:
                if _func in ['>', '<', '=', '/', '-']: #* 符号组合及多义符号的替换规范
                    _cons = re.sub(rf'\({_func}\s',self._getFunc(_func)+'(',_cons)
                else:
                    _cons = _cons.replace('('+_func,self._getFunc(_func)+'(')
            _code = _cons.replace('( ','(').replace(' ',',')
            # logger.debug(f"pre {_code}")
            import time
            for _ in varname: #! 被外部调用时，将变量对象指向临时转运类实例，避免NameError
                # logger.debug(_) #TEST 变量名
                
                # _code = re.sub(rf'^(other)[^#]{_}\s*',f'other.{_}',_code)
                # _code = re.sub(rf'\({_}',f'(other.{_}',_code)
                # _code = re.sub(rf'{_}\,',f'other.{_},',_code)
                # _code = re.sub(rf'\,{_}\)',f', other.{_}',_code) #BUG Y22AUG29L#164
                _pattern = re.compile(rf'[\(\s+(,\s+)]{_}') #UPDATE-Aug 18th 整合了匹配语句中的变量的正则表达式，统一了替换处理方法
                _patches = re.findall(_pattern, _code)
                for patch in _patches:
                    cgp = re.sub(f'{_}',f'other.{_}',patch) #* changed patch-> cgp
                    patch = patch.replace('(','\(').replace(')','\)')
                    _code = re.sub(rf'({patch})',cgp,_code)
                # logger.debug(f"do {_code}")
                # print(f">> {_code}")
                # time.sleep(2)
            if f_no_1st and _code.find('(') != _code.find(')'): #* 除首发指令外，指令间需要分隔
                _code = ',' + _code
                #DEBUG  修正分离语句的拼装 -> 由于匹配语句的正则表达式的更新不再改动右括号(#BUG Y22AUG29L#164)
                #DEBUG  组内指令封闭检查功能冗余,故删除
                # if _code.find('(') > _code.find(')'): #// * 检查封闭指令作用范围
                    # _code = _code + ')'
                    # logger.debug(f">>{_code}")
                    # time.sleep(1)
            if  f_no_1st:
                pass
            #* 越过首发指令
            else: 
                f_no_1st = True 
            
            _code = re.sub(r'(true)|(false)',self.__pattern_boolval_sub, _code) #* 逻辑值字符关键字规范
            l_code.append(_code)
            
        code = ' '.join(l_code)
        code = code.replace('#x','0x')#* 十六进制标志替换
        code = code.replace('#b','0b')#* 二进制标志替换
        # logger.debug(f"code>> {code}")#TEST 
        # sys.exit(1)
        try:
            setattr(other,'rb_s_constraints',eval(code)) #! 运行组合完成的约束重建指令，并创建临时对象来转运
            return other.__dict__['rb_s_constraints']
        except Exception as e:
            logger.error(f"约束重建失败-{e}\nErrSmt>>\n{code}")
            sys.exit(1)
    #END 
    
    #PART 3 Solves
    def _getSolve(self, other, varname:list):  #>> Core Method 字符化解集的还原重建
        assert (self.__solves is not None), AssertionError('空解')
        solves = [_ for _ in self.__solves.values()]
        
        l_code = []
        f_no_1st = False
        
        for _split in solves:
            for _solve in list(_split):
                _solve = _solve.strip()
                _solve = re.sub(r'(-)\s(\d)', self.__pattern_del_bks_sub, _solve) #* 负数规范
                _rp_f = [_ for _ in self.__func_dict.keys()]
                for _func in _rp_f:
                    if _func in ['>', '<', '=', '/', '-']: #* 符号组合及多义符号的替换规范
                        _solve = re.sub(rf'\({_func}\s',self._getFunc(_func)+'(',_solve)
                    else:
                        _solve = _solve.replace('('+_func,self._getFunc(_func)+'(')
                _code = _solve.replace('( ','(').replace(' ',',')
                
                for _ in varname: #! 被外部调用时，将变量对象指向临时转运类实例，避免NameError
                    _code = re.sub(rf'({_}),|,({_})',self.__pattern_var_sub,_code)
                    
                if f_no_1st and _code.find('(') != _code.find(')'): #* 除首发指令外，指令间需要分隔
                    _code = ',' + _code

                if  f_no_1st:
                    pass
                #* 越过首发指令
                else: 
                    f_no_1st = True 
                
                _code = re.sub(r'(true)|(false)',self.__pattern_boolval_sub, _code) #* 逻辑值字符关键字规范
                l_code.append(_code)
                
        code = ' '.join(l_code)
        code = code.replace('#x','0x')#* 十六进制标志替换
        try:
            if len(code) == 0 or code.isspace():
                setattr(other,'rb_v_constraints',True)
            else:
                # logger.debug(f"$  {code}")#TEST 
                setattr(other,'rb_v_constraints',eval(code)) #! 运行组合完成的约束重建指令，并创建临时对象来转运
            return other.__dict__['rb_v_constraints']
        except Exception as e:
            logger.error(f"解集还原失败-{e}\nErrSmt>>\n{code}")
    
    def _setSolve(self, solves):
        self.__solves = solves
    
    #PART 4 Object Effectiveness 
    def _getStatus(self):
        return self.__surviving
    
    def _setStatus(self, status:bool):
        self.__surviving = status
    #END 
    
    #PART 5 Object Flag
    def _getFlag(self): #TODO 标志类的作用明确
        return self.__flag
    
    def _setFlag(self, complement:str):
        # _id = hash(complement) #DEBUG PEP 456 python的hash涉及随机化(加盐)
        _comp = re.split('\n', complement)
        self.__flag = FlagUtil(complement=_comp)
    #END 
    
    ##PART EX Func MOD
    def _getFunc(self, _func:str):
        return self.__func_dict[_func]
    
    @staticmethod
    def _del_other(other):
        '''释放临时交换类的实例对象'''
        # logger.debug(f' {other} 临时交换类实例已释放')
        del other
    
    @staticmethod
    def __pattern_del_bks_sub(match):
        '''处理负数表述中的多余空格'''
        return match.group(1) + match.group(2)
    
    @staticmethod
    def __pattern_boolval_sub(match):
        '''处理逻辑值的字符转换'''
        _sub = match.group(0)
        _sub = _sub[0].upper() + _sub[1:]
        return _sub
    
    @staticmethod
    def __pattern_var_sub(match):
        '''处理不同位置的变量替换'''
        _sub = match.group(0)
        _var = match.groups()
        if match.group(1):
            return _sub.replace(_var[0],f'other.{_var[0]}')
        elif match.group(2):
            return _sub.replace(_var[1],f'other.{_var[1]}')
        else:
            logger.warning('未知匹配')
            return ''
        
    #END 
# if __name__ == '__main__' :
#     x = z3.Int('x')
#     y = z3.Bool('y')
#     z = z3.String('z')
#     # u = z3.BitVec('u',16) #TEST 未实现转换对象的识别和处理
    
#     #PART step 1 #
#     names = []
#     funcs = []
#     # for obj in [x,y,z,u]:
#     for obj in [x,y,z]:
#         names.append(obj.sexpr())
#         if isinstance(obj,z3.ArithRef):
#             _z3Func = 'Real' if obj.is_real() else 'Int'
#         elif isinstance(obj,z3.BoolRef):
#             _z3Func = 'Bool'
#         elif isinstance(obj,z3.SeqRef):
#             _z3Func = 'String'
#         else:
#             _z3Func = 'unknown' #TODO 更多变量类型封装
#         funcs.append(_z3Func)
    
#     varset_dict = dict(zip(names,funcs))
#     ##PART TEST step 1 ##
#     # print(varset_dict)
#     ##END
#     utils = SolveUtil()
#     # _objs = TObjUtil()
#     utils._setVars(varset_dict)
#     vars = utils._getVars(TObjUtil())
#     print(vars)
#     # print(dir(_s))
#     #END
    
#     #PART step 2 #
#     cons = And(x>=15,x>-10,Or(x!=2, And(x!=3,x!=1)), Not(x==0)).sexpr()
#     utils._setCons(cons)
#     # c = utils._getCons(TObjUtil())
#     c = utils()
#     # print(dir(_objs))
#     # utils._del_other(_objs)
#     _s = Solver()
#     _s.add(c)
#     if _s.check() == sat:
#         # print(_s.model())
#         pass
#     #END
#     # print(dir(SolveUtil))