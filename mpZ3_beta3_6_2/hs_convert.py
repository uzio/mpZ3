'''
Author: Uzio
Date: 2022-06-23 10:16:21
Email: 1336299411@qq.com
LastEditors:  
LastEditTime: 2022-08-25 15:52:44
Description: 
version:  
'''
def str_to_hex(s):
    # 文本转16进制 
    return ' '.join([hex(ord(c)).replace('0x', '') for c in s])

def hex_to_str(s):
    #16进制转为文本
    try:
        res = ''.join([chr(i) for i in [int(b, 16) for b in s.split(' ')]])
        return res
    except Exception as e:
        print(f"hexstr:{[int(b, 16) for b in s.split(' ')]} - {e}")
    # return ''.join([chr(i) for i in [int(b, 16) for b in s.split(' ')]])

