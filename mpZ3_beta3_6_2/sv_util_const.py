'''
Author: Uzio
Date: 2022-04-19 22:38:42
Email: 1336299411@qq.com
LastEditors:  
LastEditTime: 2022-04-20 17:17:09
Description: 常量操作数定义
version: 1.0
'''
# encoding : utf-8
import enum
from enum import IntEnum

class UtilConst(IntEnum):
    OP_S = 1 #* 解算器操作
    OP_V = 2 #* 验证器操作
    
    MP_ON = 8
    MP_OFF = 0