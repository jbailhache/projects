# -*- coding: iso-8859-15 -*-
import os
import sys
os.chdir('\\carte mémoire\\python')
execfile('load.py')
cours=lirecourslf(['\\carte mémoire\\bourse\\cours\\srd-0911.xls'])
execfile('lc.py')
#print(valor(pf))
#sys.stdin.readline()
while 1:
 a=raw_input()
 if a=='':
  break
 graphid(a)



