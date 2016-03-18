
a = [[1,2],[3,4]]
print a
print len(a)
print len(a[0])
print type(a)
print type([])
print type(1)

def max(a,b):
  if (a>b): return a
  return b

def add(a,b):
  if type(a)==type([]):
    if type(b)==type([]):
      n=max(len(a),len(b))
      c = [0 for i in range(0,n)]
      for i in range(0,n):
        if len(a)>i:
          if len(b)>i:
            c[i] = add(a[i],b[i])
          else:
            c[i] = a[i]
        else:
          c[i] = b[i]
    else:
      c = [add(a[i],b) for i in range(0,len(a))]
  elif type(b)==type([]):
    c = [add(a,b[i]) for i in range(0,len(b))]
  else:
    c = a + b
  return c

print add(3,5)
print add(40,[1,2,3])
print add([1,2,3],50)
print add([1,2,3],[10,20,30])
print add(a,a)
  

def prodex(a,b):
  if type(a)!=type([]):
    if type(b)!=type([]):
      return a * b
    else:
      return [prodex(a,b[i]) for i in range(0,len(b))]
  else:
    return [prodex(a[i],b) for i in range(0,len(a))]

print prodex(10,[1,2,3])
print prodex([4,5,6],100)
print prodex([1,2,3],[10,100])

def diagof(a):
   return [a[i][i] for i in range(0,len(a))]

a = [[1,2,3],[4,5,6],[7,8,9]]
print diagof(a)

def sum(a):
  s = 0
  if type(a)!=type([]):
    return a
  for x in a:
    s = add(s,x)
  return s

print sum(5)
print sum([1,2,3,4])
print sum(a)

def trace(a):
  return sum(diagof(a))

print trace(a)

def prod1(a,b):
  return trace(prodex(a,b))

print prodex(a,a)
print diagof(prodex(a,a))
print sum(diagof(prodex(a,a)))
print prod1(a,a)

def item(x,i):
  if (i<len(x)):
    return x[i]
  else:
    return 0.0

def rect(a):
  if type(a) != type([]):
    return a
  if type(a[0]) != type([]):
    return a
  max = 0
  for x in a:
    if len(x) > max:
      max = len(x)
  b = [[item(x,i) for i in range(0,max)] for x in a]
  return b

def transpose(a):
  a = rect(a)
  if type(a)!=type([]):
    return a
  elif type(a[0])!=type([]):
    return [a]
  else:
    return [[a[i][j] for i in range(len(a))] for j in range(len(a[0]))]

print transpose(6)
print transpose([1,2,3])
print transpose(a)

def prodmat1(a,b):
  return prod1(transpose(a),b)

print prodmat1(a,a)

b = [[1,2],[3,4]]

print prodmat1(b,b)
print prodex(b,b)
print prod1(b,b)
print prod1(b,transpose(b))

def prod(a,b):
  if type(a)!=type([]):
    return prodex(a,b)
  elif type(b)!=type([]):
    return prodex(a,b)
  else:
    s = 0
    for i in range(len(a)):
      s = add (s, prodex(a[i],b[i]))
    return s

print prod(b,b)
print prod(transpose(b),b)
print prod(b,transpose(b))

def prodmat(a,b):
  return prod(transpose(a),b)

print prodmat(a,a)
print prodmat(b,b)

def normeligne(a):
  max = 0
  for i in range(len(a)):
    s = 0
    for j in range(len(a[0])):
      s = s + abs(a[i][j])
    if s > max:
      max = s
  return max

print normeligne(a)

def normecolonne(a):
  max = 0
  for i in range(len(a[0])):
    s = 0
    for j in range(len(a)):
      s = s + abs(a[j][i])
    if s > max:
      max = s
  return max

print normecolonne(a)

def zero(n):
  a = [[0 for j in range(n)] for i in range(n)]
  return a

print zero(3)

def fif(c,a,b):
  if c:
    return a
  else:
    return b

def id(n):
  a = [[fif(i==j,1,0) for j in range(n)] for i in range(n)]
  return a

print id(3)

def norme2(a):
  if type(a)!=type([]):
    return a*a
  s = 0
  for x in a:
    s = s + norme2(x)
  # print 'norme2=', s
  return s

def norme(a):
  return norme2(a)**0.5
    
def inv(A):
  d = len(A)
  I = id(d)
  B = prodex (1/float(normeligne(A)*normecolonne(A)), transpose(A))
  E = add (I, prodex (-1,
 prodmat(B,A)))
  e = norme2(E)
  i = 0
  while norme2(E) > 0.0000000000001 and i<100:
    # print 'boucle inv'
    B = prodmat (add(I,E), B)
    E = add (I, prodex (-1, prodmat(B,A)))
    e1 = e
    e = norme2(E)
    i = i + 1
    if i>6 and e>e1:
      break
  return B

def puissance1(a):
  n = len(a)
  u = [0 for i in range(n)]
  u[0] = 1
  v = u
  l = 0
  l1 = 1
  while abs(l-l1) > 0.00001:
    l1 = l
    t = prodmat (a, u)
    l = prod (v, t)
    u = prodex (1/l, t)
  lr = l
  vr = prodex(1/(prod(u,u)**0.5),u)
  return [lr,vr]

def puissance(a):
  n = len(a)
  x = [0 for i in range(n)]
  x[0]= 1
  l = 0
  l1 = 1
  while abs(l-l1) > 0.00001:
    l1 = l
    b = prodex (1/norme(x), x)
    x = prodmat(a,b)
    l = prod(b,x)
  return [l,b]

def deflation1(a,nvp):
  ls = [[] for i in range(nvp)]
  us = [[] for i in range(nvp)]  
  b = a
  for k in range(nvp):
    lu = puissance(b)
    l = lu[0]
    u = lu[1]
    ls[k] = l
    us[k] = u 
    mv = puissance(transpose(b))
    m = mv[0]
    v = mv[1]
    b = add (a, prodex (-1, prodex (u, v)))
  return [ls, us]
  
def deflation2(a,nvp):
  n = len(a)
  as1 = [[] for i in range(n)]
  as1[0] = a
  ls = [[] for i in range(nvp)]
  us = [[[0 for k in range(n)] for j in range(n)] for i in range(n)]
  b = a
  for k in range(nvp):
    lu = puissance(b)
    l = lu[0]
    u = lu[1]
    ls[k] = l
    us[k][k] = u 
    mv = puissance(transpose(b))
    m = mv[0]
    v = mv[1]
    b = add (a, prodex (-1, prodex (u, v)))
  return [ls, us]
  
def deflationlme(a,nv):
  n = len(a)
  ak = [[[0 for k in range(n)] for j in range(n)] for i in range(n)]
  ak[0] = a
  w = [[0 for j in range(n)] for i in range(n)]
  l = [0 for i in range(n)]
  xk = [[[0 for k in range(n)] for j in range(n)] for i in range(n)]
  for k in range(n):
    lx = puissance(ak[k])
    l1 = lx[0]
    x = lx[1]
    l[k] = l1
    xk[k][k] = x
    tk = k
    for p1 in range(k-1):
      p = k-2-p1
      tp = p
      tw = w[p]
      txk = xk
      txk1 = xk[p+1][k]
      q = prod (w[p], xk[p+1][k])
      if (l[k] == l[p]):
        c=0
      else:
        c=l[p]/(l[k]-l[p])
      q = prodex (q, c)
      xk[p][k] = prodex (xk[p][k], 1/prod(xk[p][k],xk[p][k])**0.5)
    if k>=nv or k>=n:
      lambd = l
      u = xk[1]
      return [lambd,u]
    tk = k
    tx = x
    w[k] = prodex (xk[k][k], 1/prod(xk[k][k],xk[k][k]))
    ak[k+1] = add (ak[k], prodex (-l[k], prod(xk[k][k],w[k]))) 

def deflation(a):
  d = len(a)
  ak = [[] for i in range(d)]
  ak[0] = a
  xk = [[] for i in range(d)]
  w = [[0 for j in range(d)] for i in range(d)]
  l = [0 for i in range(d)]
  for k in range(d):
    rp = puissance(ak[k])
    l[k] = rp[0]
    xk[k] = [[0 for j in range(d)] for i in range(d)]
    xk[k][k] = rp[1]
    r = range(k)
    # print k
    # print r
    r.reverse()
    # print r
    for p in r:
      # print p
      q = prod(w[p],xk[p+1][k])
      if l[k] == l[p]:
        c = 0
      else:
        c = l[p] / float(l[k] - l[p])
      q = q * c
      xk[p][k] = add (xk[p+1][k], prodex (q, xk[p][p]))
    if (k >= d-1):
      return [l, xk[0]]
    r = prod (xk[k][k], xk[k][k])
    w[k] = prodex (1/float(r), xk[k][k])
    ak[k+1] = add (ak[k], prodex (-l[k], prodex (xk[k][k], w[k])))
  return [l, xk[0]]


  


    
  
