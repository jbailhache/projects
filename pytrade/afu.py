
def map1(x,f):
  y=[]
  for a in x:
    y=y+[f(a)]
  return y

def map1p(x,p,f):
  y=[]
  for a in x:
    y=y+[f(a,p)]
  return y

def map2(x,y,f):
  z=[]
  n=min(len(x),len(y))
  for i in range(n):
    z=z+[f(x[i],y[i])]
  return z

def afu(y):
  y1=transpose(y)
  v=map2(y1,y1,prod)
  w=sum(v)
  print 'w=',w
  iw=inv(w)
  print 'iw=',iw
  x=map1(y,sum)
  s=prod(iw,prod(x,x))
  [l,u]=deflation(s)
  c=map1p(y,transpose(u),prodmat)
  return [s,l,u,c]

def afud(y,d):
  y1=transpose(y)
  print 'y=', y
  print 'y1=', y1
  print 'd=', d
  v=[]
  for xi in y1:
    v=v+[prod(prod(d,xi),xi)]
  w=sum(v)
  print 'w=',w
  iw=inv(w)
  print 'iw=',iw
  x=map1(y,sum)
  s=prod(iw,prod(prod(d,x),x))
  [l,u]=deflation(s)
  c=map1p(y,transpose(u),prodmat)
  return [s,l,u,c]

def red(x):
  r=matred(x)
  y=prodmat(x,r)
  return y

def acpbn(z):
  s=prod(z,z)
  lu=deflation(s)
  c=prodmat(z,transpose(lu[1]))
  return [s,lu,c]

def diag(v):
  n=len(v)
  d=[[0 for i in range(n)] for j in range(n)]
  for i in range(n):
    d[i][i]=v[i]
  return d

def id(n):
  d=[[0 for i in range(n)] for j in range(n)]
  for i in range(n):
    d[i][i]=1
  return d

def data_afu_acp(x1):
  x = prodex (1/float(len(x1))**0.5, centred(x1))
  y=[]
  for l in x:
    y=y+[diag(l)]
  return y

y1=[[[1,2,0],[3,4,0]],[[0,0,5],[0,0,6]]]
x1=sum(y1)
print x1

y=transpose(y1)
print y
x=map1(y,sum)
print x
y2=map1(y,transpose)
print y2
y1=transpose(y)
v=map2(y1,y1,prod)
print v
w=sum(v)
print w
iw=inv(w)
print iw
s=prod(iw,prod(x,x))
print s

yacp=[[[1,0],[0,2]],[[3,0],[0,4]],[[5,0],[0,6]]]
xacp=map1(yacp,sum)
xacpr=red(xacp)
xacps=prodex(float(len(xacp))**0.5,xacpr)
sluc1=acpbn(xacpr)
sluc2=acpb(xacps)
sluc3=afu(yacp)
r=matred(xacp)
xacpr=prodmat(xacp,r)
s1=prod(xacpr,xacpr)
y1=transpose(yacp)
v=map2(y1,y1,prod)
w=sum(v)
iw=inv(w)
xx=prod(xacp,xacp)
s3=prod(iw,xx)

xacp=[[1,3,4],[4,5,2],[6,1,8],[9,5,8]]
xacpcr=centred(xacp)
sluc4=acpb(xacpcr)
yacpcr=data_afu_acp(xacp)
sluc5=afu(yacpcr)
c4=sluc4[2]
c5=prodex ( len(xacp)**0.5 , sum(transpose(sluc5[3])) )
sluc6=afud(yacpcr,id(len(yacpcr)))
c6=prodex ( len(xacp)**0.5 , sum(transpose(sluc6[3])) )

