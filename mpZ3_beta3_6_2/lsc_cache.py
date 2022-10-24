'''
Author: Uzio
Date: 2022-10-24 09:37:44
Email: 1336299411@qq.com
LastEditors:  
LastEditTime: 2022-10-24 09:42:22
Description: 
version:  
'''
'''
Author: Uzio
Date: 2022-05-10 16:11:53
Email: 1336299411@qq.com
LastEditors:  
LastEditTime: 2022-05-17 20:06:24
Description: 最近生存检查缓存(Last Survival Check Cache)
version: 1.0
'''
import os
from typing import Any

### PART 1 ###
def cache(func):
    data={}
    
    def wrapper(n):
        if n in data:
            return data[n]
        else:
            res = func(n)
            data[n] = res
            return res
    
    return wrapper

### PART 2 ###
class Node(object):
    '''
    结点
    '''
    def __init__(self, prev=None, next=None, key=None, value=None) -> None:
        self.prev, self.next, \
        self.key, self.value = prev, next, key, value
        
class CircularDoubleLinkedList(object):
    '''
    双向链表
    '''
    def __init__(self) -> None:
        node = Node()
        node.prev, node.next = node, node
        self.rootnode = node
        
    def headnode(self):
        return self.rootnode.next
    
    def tailnode(self):
        return self.rootnode.prev
    
    def remove(self, node):
        if node is self.rootnode:
            return
        else:
            node.prev.next = node.next
            node.next.prev = node.prev
            
    def append(self, node):
        tailnode = self.tailnode()
        tailnode.next = node
        node.next = self.rootnode
        self.rootnode.prev = node
        
class LSCCache(object): #TODO* 在最近最少使用缓存的基础上融合生存检查机制
    '''
    Last Survival Check Cache ,删除最近失效单元的缓存
    '''
    def __init__(self, maxsize=16) -> None: #TODO 最大大小设定值
        self.maxsize = maxsize
        self.cache = {}
        self.access = CircularDoubleLinkedList()
        self.isfull = len(self.cache) >= self.maxsize #TODO* 失效数据单元检查
    
    def __call__(self, func) -> Any:
        def wrapper(n):
            cachenode = self.cache.get(n)
            if cachenode is not None: # hit
                self.access.remove(cachenode)
                self.access.append(cachenode)
                return cachenode.value
            else: # miss
                value = func(n)
                if not self.isfull:
                    tailnode = self.access.tailnode()
                    newnode = Node(tailnode, self.access.rootnode, n, value)
                    self.access.append(newnode)
                    self.cache[n] = newnode
                    
                    self.isfull = len(self.cache) >= self.maxsize
                    return value
                else: # full
                    lscnode = self.access.headnode()
                    del self.cache[lscnode.key]
                    self.access.remove(lscnode)
                    tailnode = self.access.tailnode()
                    newnode = Node(tailnode, self.access.rootnode, n, value)
                    self.access.append(newnode)
                    self.cache[n] = newnode
                return value
        
        return wrapper
