
ohbc = 1

nq = 9
ny = 7
ne = 1
nl = 1
nd = nq + nq * (nq + ny)

# if ohbc:
#   nd=nq*(nq+6)
#   ny=5
# else:
#   nd = nq * (nq + 3)
#   ny=2

def qimtnqc(x,nq):
  if len(x) != nd:
    print '*** erreur : len(x)=', len(x), ' x=', x
  qi = [x[i] for i in range(nq)]
  print 'len(x)=',len(x),' nq=',nq
  mt = [[x[nq+(nq+2)*i+j] for j in range(nq+2)] for i in range(nq)]
  # suppression des termes constants
  # for i in range(nq):
  #   mt[i][nq+1] = 0
  return [qi,mt]

def qimtnqohbc(x,nq):
  if len(x) != nd:
    print '*** erreur : len(x)=', len(x), ' x=', x
  qi = [x[i] for i in range(nq)]
  print 'len(x)=',len(x),' nq=',nq
  mt = [[x[nq+(nq+5)*i+j] for j in range(nq+5)] for i in range(nq)]
  # suppression des termes constants
  # for i in range(nq):
  #   mt[i][nq+1] = 0
  return [qi,mt]

def qimtnqny(x,nq,ny):
  if len(x) != nd:
    print '*** erreur : len(x)=', len(x), ' x=', x
  qi = [x[i] for i in range(nq)]
  print 'len(x)=',len(x),' nq=',nq
  mt = [[x[nq+(nq+ny)*i+j] for j in range(nq+ny)] for i in range(nq)]
  # suppression des termes constants
  # for i in range(nq):
  #   mt[i][nq+1] = 0
  return [qi,mt]

def qimtnqnyne(x,nq,ny):
  if len(x) != nd:
    print '*** erreur : len(x)=', len(x), ' x=', x
  qi = [x[i] for i in range(nq)]
  print 'len(x)=',len(x),' nq=',nq
  lmt = [[[x[nq + e * nq*(nq+ny) + (nq+ny)*i + j] for j in range(nq+ny)] for i in range(nq)] for e in range(ne)]
  return [qi,lmt]

def qimtnq1(x,nq):
  if ohbc:
    return qimtnqohbc(x,nq)
  else:
    return qimtnqc(x,nq)

def qimtnq(x,nq):
  return qimtnqny(x,nq,ny)

# def qimt(x):
#   return qimt(x,nq,ny)

def convertxnq(x,nq1,nq2):
  global nq,nd
  nq0=nq
  nd0=nd
  if nq1<nq2: nqmin=nq1
  else: nqmin=nq2
  nq=nq1
  nd=nq*(nq+3)
  print 'nq1=',nq1,' nq2=',nq2
  qm=qimtnqc(x,nq1)
  qi=[0.0 for i in range(nq2)]
  mt=[[0.0 for j in range(nq2+ny)] for i in range(nq2)]
  for i in range(nqmin):
    qi[i]=qm[0][i]
  print 'nqmin=',nqmin
  for i in range(nqmin):
    for j in range(nqmin):
      mt[i][j]=qm[1][i][j]
  for i in range(nqmin):
    if ohbc:
      mt[i][nq2+3]=qm[1][i][nq1]
      mt[i][nq2+3]=qm[1][i][nq1+1]
    else:
      mt[i][nq2]=qm[1][i][nq1]
      mt[i][nq2+1]=qm[1][i][nq1+1]
  nq=nq2
  nd=nq*(nq+3)
  y=vecteurqimt(qi,mt)
  nq=nq0
  nd=nd0
  return y

def convertxnqny(x,nq1,ny1,nq2,ny2):
  global nq,nd
  nq0=nq
  nd0=nd
  if nq1<nq2: nqmin=nq1
  else: nqmin=nq2
  nq=nq1
  # nd=nq*(nq+3)
  nd = nq * (1 + nq + ny)
  print 'nq1=',nq1,' nq2=',nq2
  # qm=qimtnqc(x,nq1)
  qm = qimtnqny (x, nq1,ny1)
  qi=[0.0 for i in range(nq2)]
  mt=[[0.0 for j in range(nq2+ny)] for i in range(nq2)]
  for i in range(nqmin):
    qi[i]=qm[0][i]
  print 'nqmin=',nqmin
  for i in range(nqmin):
    for j in range(nqmin):
      mt[i][j]=qm[1][i][j]
  for i in range(nqmin):
    if ohbc:
      mt[i][nq2+3]=qm[1][i][nq1]
      mt[i][nq2+3]=qm[1][i][nq1+1]
    else:
      mt[i][nq2]=qm[1][i][nq1]
      mt[i][nq2+1]=qm[1][i][nq1+1]
  nq=nq2
  # nd=nq*(nq+3)
  nd = nq * (1 + nq + ny2)
  y=vecteurqimt(qi,mt)
  nq=nq0
  nd=nd0
  return y


def vecteurqilmt(qi,lmt):
  x = [0 for i in range(len(qi) + len(lmt)*len(lmt[0])*len(lmt[0][0]))]
  for i in range(len(qi)):
    x[i] = qi[i]
  for i in range(len(lmt)):
    for j in range(len(lmt[i])):
      for k in range(len(lmt[i][j])):
        x[len(qi)+i*len(lmt[i][j])+j] = lmt[i][j][k]
  return x

def convertxnqnyne(x,nq1,ny1,nq2,ny2,ne):
  global nq,nd
  nq0=nq
  nd0=nd
  if nq1<nq2: nqmin=nq1
  else: nqmin=nq2
  nq=nq1
  # nd=nq*(nq+3)
  nd = nq * (1 + nq + ny)
  print 'nq1=',nq1,' nq2=',nq2
  # qm=qimtnqc(x,nq1)
  qm = qimtnqny (x, nq1, ny1)
  qi=[0.0 for i in range(nq2)]
  # mt=[[0.0 for j in range(nq2+ny)] for i in range(nq2)]
  lmt=[[[0.0 for j in range(nq2+ny)] for i in range(nq2)] for e in range(ne)]
  for i in range(nqmin):
    qi[i]=qm[0][i]
  print 'nqmin=',nqmin
  for i in range(nqmin):
    for j in range(nqmin):
      lmt[0][i][j]=qm[1][i][j]
  for i in range(nqmin):
    if ohbc:
      lmt[0][i][nq2+3]=qm[1][i][nq1]
      lmt[0][i][nq2+3]=qm[1][i][nq1+1]
    else:
      lmt[0][i][nq2]=qm[1][i][nq1]
      lmt[0][i][nq2+1]=qm[1][i][nq1+1]
  for e in range(1,ne):
    for i in range(nq):
      lmt[e][i][i] = 1.0
  nq=nq2
  # nd=nq*(nq+3)
  nd = nq * (1 + nq + ny2)
  y=vecteurqilmt(qi,lmt)
  nq=nq0
  nd=nd0
  return y

expansex1 = expansex

def expansexnq(x,nq):
  y=expansex1(x)
  z=convertxnq(y,4,nq)
  return z

def expansexnqny(x,nq,ny):
  y=expansex1(x)
  z=convertxnqny(y,4,2,nq,ny)
  return z

def expansexnqnyne(x,nq,ny,ne):
  y=expansex1(x)
  z=convertxnqnyne(y,4,2,nq,ny,ne)
  return z

def expansex(x):
  # y=expansexnq(x,nq)
  y = expansexnqnyne (x, nq, ny, ne)
  return y

def popinitcnq(h,n,c,nq):
 l = extractexpxs(h)
 p = valeursxsc(l,c)
 r = p
 while len(r)<n:
  r = r + p
 r = r[0:n]
 return r

def popinitcnqmacd(h,n,c,nq):
 l = extractexpxs(h)
 p = valeursxsc(l,c)
 r = p
 while len(r)<n:
  r = r + p
 r = r[0:n]
 x = vecteurqimt(qi3macd,mt3macd(12,26,9))
 y = convertxnq(x,4,nq)
 v = valeurc(y,c)
 r = r + [[v,y]]
 return r


