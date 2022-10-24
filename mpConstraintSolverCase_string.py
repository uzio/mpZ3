from collections import defaultdict
import random
from mpZ3_beta3_6_2.mp_z3 import *
from mpZ3_beta3_6_2.sv_utils import *
from timeit import timeit
from mpZ3_beta3_6_2.hs_convert import str_to_hex, hex_to_str

def cmpAB(a:str,b:str):
    '''统计两条字符串相同位点'''
    stra = tuple(a)
    strb = tuple(b)
    count = 0
    for sa,sb in zip(stra,strb):
        if sa == sb:
            count += 1
    return count

def repAB(a:str,b:str):
    '''使用空格替换第二条字符串和第一条字符串不同的位点'''
    stra = tuple(a)
    strb = tuple(b)
    strc = ''
    for sa,sb in zip(stra,strb):
        if sa == sb:
            strc += sa
        else:
            strc += ' '
    return strc

def print_S8S(a, b, ahead='',bhead='', size=30, linefeed=1):
    '''并排输出两组字符串'''
    while a or b:
        print(ahead + a[:size].ljust(size) + "\n" * linefeed + bhead + b[:size])
        a = a[size:]
        b = b[size:]

def main():
    
    string_seed = "Ae86!!FG32di*%@adh5760Yk{P89fpoljasjdrklmvaimztawuehfoawm1" #* 目标约束种子
    random.seed(410)
    string = ''.join(random.choices(string_seed, k=500)) #* 目标约束-随机字符串生成
    # print(f"原文>>\n{string}")
    
    h_str = str_to_hex(string)#* 转换成16进制
    raw_string = bytearray(a2b_hex(h_str.replace(' ', ''))) #* 转换成二进制数组
    raw_string_lenth = len(raw_string)
    # for i in range(len(raw_string) // 2): # 翻转
    #     c = raw_string[i]
    #     raw_string[i] = raw_string[len(raw_string) - i - 1]
    #     raw_string[len(raw_string) - i - 1] = c
    aim = [z3.BitVec(f'aim{i}', 32) for i in range(len(raw_string))] #*针对该数组创建位向量数组
    
    #* 校验码
    # encrypt = list(reversed(raw_string))
    
    # for i,arg in enumerate(encrypt):
    #     if arg <= encrypt[raw_string_lenth-i-1]:
    #         continue
    #     else:
    #         encrypt[i] = raw_string[i]
    
    proof = []
    encrypt = list(reversed(raw_string))
    for i,arg in enumerate(encrypt):
        try:
            if arg <= encrypt[raw_string_lenth-i-1]:
                proof.append(raw_string[raw_string_lenth-i-1])
            else:
                proof.append(raw_string[i])
        except Exception as e:
            print(f"i: {i}, len: {len(encrypt)} exception:{e}")    
            exit()
            
    proof_str = "".join([chr(s) for s in proof])
    # print(f"密文>>\n{proof_str}")
    
    print_S8S(string, proof_str, "原码>> ", "校验$$ ", size=80)
    similar = cmpAB(string, proof_str)
    print(f"\n加密位数: {len(string)-similar}")
    
    global c
    def do_mp():
        mps = mpZ3Solver(UC.MP_ON)
        
        for i in range(raw_string_lenth):
            mps.add(z3.If(aim[i]>aim[raw_string_lenth-i-1], aim[i] == raw_string[raw_string_lenth-i-1], aim[i] == raw_string[i]))
        
        res = mps.solve(*aim)
        
        #! 统计各变量获得的解数量 & 规范处理输出
        _count = {}
        _set = defaultdict(list)
        for r in res:
            group = r.strip('(').strip(')').split(' ')
            var = group[1]
            val = group[2]
            _count[var] = _count.get(var,0) + 1
            _set[var].append(val.replace('#x','0x'))
        
        _maaimSov = max(_count.values()) #解的最大计数
        
        for k,v in _set.items():
            sub = _maaimSov - len(v)
            if sub > 0:
                _set[k].extend(['0x20']*sub) # 空格补位
            else:
                continue
        print(f"多进程联合求解$\n字符串原型>>{string}\n")
        
        for serial in range(_maaimSov):
            ir = (int(v[serial], 16) for v in _set.values())
            sr = ''.join(chr(s) for s in (r if r <=255 else 32 for r in ir))#.replace(' ','')
                
            
            similar = cmpAB(proof_str, sr)
            correctratio = 100*(similar/len(proof_str))
            simiResult = repAB(proof_str, sr)
            global c 
            c = serial+1
            print("-----------------------")
            print(f"第{str(serial+1).rjust(2,'0')}次结果>>{sr}\n")
            print(f"匹配#")
            print_S8S(proof_str, simiResult, "目标>> ", "破译<< ", size=80)
            print(f"匹配精度: {correctratio:.4f}%\n")
        
    mp_time = timeit(do_mp,number=1)
    print(f"多进程总耗时: {mp_time:.4f}s , 平均 {mp_time/c:.4f} s/次")
    def do_sg():
        flags = []
        single_Sov = mpZ3Solver(UC.MP_OFF)
        for i in range(raw_string_lenth):
            single_Sov.push()
            single_Sov.add(z3.If(aim[i]>aim[raw_string_lenth-i-1], aim[i] == raw_string[raw_string_lenth-i-1], raw_string[i] == encrypt[i]))
        

            if single_Sov.check() == z3.sat:
                model = single_Sov.model()
                flag = ''
                for i in range(len(raw_string)):
                    try:
                        flag += chr(model[aim[i]].as_long().real)
                    except Exception as err:
                        flag += ' '
                flags.append(flag.replace('\x00','').replace('\t','').replace(' ',''))
            else:
                flags.append('???') # 无解情况
            single_Sov.pop()
        flags_str = "".join(flags)
        
        similar = cmpAB(proof_str, flags_str)
        correctratio = 100*(similar/len(proof_str))
        simiResult = repAB(proof_str, flags_str)
        print(f"单进程连续求解$\n字符串原型>>{proof_str}\n\n单模型结果>>{flags_str}\n")
        print(f"匹配#")
        print_S8S(proof_str, simiResult, "目标>> ", "破译<< ", size=80)
        print(f"匹配精度: {correctratio:.4f}%\n")
        
    sg_time = timeit(do_sg,number=1) 
    print(f"单进程总耗时: {sg_time:.4f}s")

if __name__ == "__main__":
    main()
    