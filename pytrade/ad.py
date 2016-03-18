
def centre(x):
  return prodex(1/float(len(x)),sum(x))

def centrer(x):
  return add (x, prodex (-1, prodex ([1 for i in range(len(x))], centre(x))))

def variance(a):
  v = [0 for i in range(len(a[0]))]
  for i in range(len(a[0])):
    # for j in range(len(a[0])):
    for j in range(len(a)): 
      v[i] = v[i] + a[j][i] ** 2
  return v

def matred (a):
  v = variance(a)
  r = [[0 for j in range(len(a[0]))] for i in range(len(a[0]))]
  for i in range(len(a[0])):
    s = v[i] ** 0.5
    if s == 0:
      r[i][i] = 1
    else:
      r[i][i] = 1/float(s)
  return r

def centred(x):
  y = centrer(x)
  r = matred(y)
  z = prodmat(y,r)
  return z

def acpb(z):
  s = prodex (1/float(len(z)), prod(z,z))
  lu = deflation(s)
  c = prodmat (z, transpose(lu[1]))
  return [s, lu, c]

x = [[1,3,4],[2,5,9],[8,0,3],[5,9,8]]

def variance(y):
  n = len(y)
  v = [0 for i in range(len(y[0]))]
  for l in y:
    for i in range(len(l)):
      v[i] = v[i] + l[i]*l[i]
  return v

def dinvs2(y):
  v = variance(y)
  n = len(v)
  d = [[0 for i in range(n)] for j in range(n)]
  for i in range(n):
    d[i][i] = 1/float(v[i])
  return d

def acp(z):
  y=centrer(z)
  # print 'y=',y
  s = prodex (1/float(len(y)), prod(y,y))
  # print 's=',s
  lu = deflation(s)
  # print 'lu=',lu
  # return lu
  c = prodmat (y, transpose(lu[1]))
  # c = prodmat ([y], transpose(lu[1])) [0]
  return [s, lu[0], lu[1], c]

  