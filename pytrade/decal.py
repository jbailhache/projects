
def decal1(c,n):
 d=[]
 for a in c:
  i=randint(0,n)
  d=d+[a[i:i+len(a)-n]]
 return d

def decal(c,n):
 d=[]
 for a in c:
  i=randint(0,len(a)-n)
  d=d+[a[i:i+n]]
 return d
