
execfile('load.py')

c=lirecourslf(['cours/srd-0901.xls'])

def libs(c):
 l=[]
 for c1 in c:
  l=l+[c1[0][1]]
 return l

def dates(c):
 d=[]
 for c1 in c[0]:
  d=d+[c1[2]]
 return d

def cld(c,l,d):
 for cl in c:
  if cl[0][1][0:len(l)]==l:
   for r in cl:
    if r[2]==d:
     return r

def var(c,il,id,ic):
 return c[il][id][ic]-c[il][id-1][ic]

def fp(c):
 l=libs(c)
 d=dates(c) 
