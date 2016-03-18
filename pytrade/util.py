
def comb(l,n):
  if n<1:
    return [[]]
  c=comb(l,n-1)
  r=[]
  for d in c:
    for x in l:
      r=r+[d+[x]]
  return r

def sign(x):
  if x==0:
    return 0
  elif x>0:
    return 1
  else:
    return -1

