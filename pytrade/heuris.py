
from random import *
from math import *

wd=600	
wd2=900
hg=600

nq = 4
# nq = 3
nd = nq * (nq + 3)
def qimt(x):
  qi = [x[i] for i in range(nq)]
  mt = [[x[nq+(nq+2)*i+j] for j in range(nq+2)] for i in range(nq)]
  # suppression des termes constants
  # for i in range(nq):
  #   mt[i][nq+1] = 0
  return [qi,mt]

def vecteurqimt(qi,mt):
  x = [0 for i in range(len(qi) + len(mt)*len(mt[0]))]
  for i in range(len(qi)):
    x[i] = qi[i]
  for i in range(len(mt)):
    for j in range(len(mt[i])):
      x[len(qi)+i*len(mt[i])+j] = mt[i][j]
  return x

# MME generalisee
# nq = 2
# nd = 4

def qimt2(x):
  qi = [0, 1]
  mt = [[0, x[0], x[1], 0], [0, x[2], x[3], 0]]
  return [qi,mt]

# nq=2
# nd=6
def qimt2a(x):
  qi = [x[0],x[1]]
  mt = [[0, x[2], x[3], 0], [0, x[4], x[5], 0]]
  return [qi,mt]

def qimt2b(x):
  qi = [0,1]
  mt = [[x[0], x[1], x[2], 0], [x[3], x[4], x[5], 0]]
  return [qi,mt]

def qimt2c(x):
  qi = [0,1]
  mt = [[0, x[0], x[1], x[2]], [0, x[3], x[4], x[5]]]
  return [qi,mt]

# nq = 2
# nd = 2
def qimt3(x):
  qi = [0, 1]
  mt = [[0, cos(x[0]*pi/4.0), sin(x[0]*pi/4.0), 0], [0, 1-x[1], x[1], 0]]
  return [qi,mt]

# nq = 2
# nd = 3
def qimt3b(x):
  qi = [0, 1]
  mt = [[0, cos(x[0]*pi/4.0), sin(x[0]*pi/4.0), 0], [0, x[1], x[2], 0]]
  return [qi,mt]
# pas de coefficient du signal ni terme constant
# nd = nq * (nq + 1)
def qimt4(x):
  qi = [x[i] for i in range(nq)]
  mt = [[0 for j in range(nq+2)] for i in range(nq)]
  for i in range(nq):
    for j in range(nq):
      mt[i][j+1] = x[nq+nq*i+j]
  return [qi,mt]

# Q0 = 0 1 0, MT = 0 . . . 0
#                  0 . . . 0
#                  0 . . . 0
# pas de coef signal ni terme constant
# nd = nq * nq
def qimt5(x):
  qi = [0 for i in range(nq)]
  qi[1] = 1
  mt = [[0 for j in range(nq+2)] for i in range(nq)]
  for i in range(nq):
    for j in range(nq):
      mt[i][j+1] = x[nq*i+j]
  return [qi,mt]

def valeur1(x):
  p = qimt(x)
  r = moyind (select, calculind4, p)
  return r[0]

def valeur(x):
  p = qimt(x)
  kd = calculind3(coursval(cours,'ALTEN'),p)
  r = kd[0]
  return [r / float(l0),kd[1]]

def valeurv(x,v):
  p = qimt(x)
  kd = calculind3(coursval(cours,v),p)
  r = kd[0]
  return [r / float(l0),kd[1]]

def valeurcv(x,cv):
  p = qimt(x)
  kd = calculind3(cv,p)
  r = kd[0]
  return [r / float(l0),kd[1]]

def valeur3(x):
  p = qimt(x)
  r1 = calculind4(coursval(cours,'PPR'),p)[0]
  r2 = calculind4(coursval(cours,'AXA'),p)[0]
  r = (r1+r2) / 2.0 
  return [r / float(l0),[]]

def valeur4(x):
  p = qimt(x)
  r1 = calculind4(coursval(cours1,'PPR'),p)[0]
  r2 = calculind4(coursval(cours2,'PPR'),p)[0]
  r = (r1+r2) / 2.0 
  return [r / float(l0),[]]

def valeur5(x):
  p = qimt(x)
  kd1 = calculind3(coursval(cours1,'PPR'),p)
  r1 = kd1[0]
  kd2 = calculind3(coursval(cours2,'PPR'),p)
  r2 = kd2[0]
  kd3 = calculind3(coursval(cours1,'AXA'),p)
  r3 = kd3[0]
  kd4 = calculind3(coursval(cours2,'AXA'),p)
  r4 = kd4[0]
  r = min(min(r1,r2),min(r3,r4))
  return [r / float(l0),kd1[1],kd2[1],kd3[1],kd4[1]]

def valeurs(x):
  p=qimt(x)
  lkd=[0,0,0]
  lkd[0]=calculind3(coursval(cours1,'PPR'),p)
  lkd[1]=calculind3(coursval(cours2,'AXA'),p)
  lkd[2]=calculind3(coursval(cours3,'HERMES'),p)
  return [[lkd[i][0]/float(l0) for i in range(3)],[lkd[i][1] for i in range(3)]]

def valeurslc(x,lc):
  p=qimt(x) 
  # print ' lc=', lc
  lkd=[calculind3(c,p) for c in lc]
  r=[[kd[0]/float(l0) for kd in lkd],[kd[1] for kd in lkd]]
  return r

def heuris1():
  mk = 0
  l = [-1.0, -0.5, 0.0, 0.5, 1.0]
  n = len(l)
  a = [0 for i in range(nd)]
  while 1:
    b = 0
    for i in range(nd):
      if a[i] < n-1:
        a[i] = a[i]+1
        b = 1
        break
      else:
        a[i] = 0
    print a
    if b==0: break

def heuris2():
  mk = 0
  mx = []
  l = [-1.0, -0.5, 0.0, 0.5, 1.0]
  n = len(l)
  a = [0 for i in range(nd)]
  while 1:
    b = 0
    for i in range(nd):
      if a[i] < n-1:
        a[i] = a[i]+1
        b = 1
        break
      else:
        a[i] = 0
    x = [l[a[i]] for i in range(nd)]
    kd = valeur(x)
    print mk, kd[0], x
    if kd[0] > mk:
      mk = kd[0]
      mx = x
    if b==0: break
  print mx
  return mx

def heuris3(cv):
  nm = 16
  # mks = [0 for i in range(nm)]
  # mxs = [[] for i in range(nm)]
  mkxs = [ [0,[]] for i in range(nm) ]
  l = [-1.0, -0.5, 0.0, 0.5, 1.0]
  n = len(l)
  a = [0 for i in range(nd)]
  while 1:
    b = 0
    for i in range(nd):
      if a[i] < n-1:
        a[i] = a[i]+1
        b = 1
        break
      else:
        a[i] = 0
    x = [l[a[i]] for i in range(nd)]
    kd = valeurcv(x,cv)
    #print mkxs[0][0], kd[0], x
    #if kd[0] > mk:
    #  mk = kd[0]
    #  mx = x
    for i in range(nm):
      if kd[0] > mkxs[i][0]:
        for j in range(nm-1-i):
          mkxs[nm-1-j] = mkxs[nm-2-j]
        mkxs[i] = [kd[0],x]
        break
    if b==0: break
  print mkxs
  return mkxs

def heuris4():
  c3 = lirecourslf(lnfxp[67:70])
  mkxs3 = heuris3 (coursval(c3,'HERMES'))
  print 'mkxs3 = ', mkxs3
  c2 = lirecourslf(lnfxp[69:73])
  mkxs2 = heuris3 (coursval(c2,'PPR'))
  print 'mkxs2 = ', mkxs2
  c1 = lirecourslf(lnfxp[65:69])
  mkxs1 = heuris3 (coursval(c1,'ALTEN'))
  print 'mkxs1 = ', mkxs1  
  return [mkxs1,mkxs2,mkxs3]

def testheur():
  nd = nq * (nq+3)
  x0 = [gauss(0,1) for i in range(nd)]
  dx = [gauss(0,1) for i in range(nd)]
  print x0
  print dx
  c=[]
  for i in range(-100,100):
    u = i / 500.0
    x = add (x0, prod (u, dx))
    v = valeur(x)
    print str(u) + '\t' + str(v)
    c = c + [[v]]
  courbes(c,['blue'],wd2,hg,'Test')

def plan():
  coefc = 1024
  maxi = 20
  maxj = 20
  stepa = 0.5
  stepb = 0.5
  master=Tk()
  can=Canvas(master,width=wd,height=hg,bg='white')
  can.pack(side=LEFT)
  b = Button (master, text=" ", command=btn)
  b.pack()
  co = int(wd/2.0)
  lo = int(hg/2.0)
  for i in range(-maxi,maxi+1):
    for j in range(-maxj,maxj+1):
      a = i*stepa
      b = j*stepb
      x = [a, b]
      kd = valeur(x)
      k = kd[0]-1
      print str(a) + '\t' + str(b) + '\t' + str(k)
      # color = '#%02x%02x%02x' % (0,min(int(k*128),255),0)
      if k < 0:
        # color = '#%02x%02x%02x' % (min(int(-k*512),255),0,0)
        color = '#%02x%02x%02x' % (255, max(0,int(255+k*coefc)),max(0,int(255+k*coefc)))
      if k == 0:
        color = 'white'
      if k > 0:
        # color = '#%02x%02x%02x' % (0,min(int(k*512),255),0)
        color = '#%02x%02x%02x' % (max(0,int(255-k*coefc)),255,max(0,int(255-k*coefc)))
      c1 = int(wd/2.0*(1+1/float(maxi+1)*(a/float(stepa)-0.5)))
      c2 = int(wd/2.0*(1+1/float(maxi+1)*(a/float(stepa)+0.5)))
      l1 = int(hg/2.0*(1-1/float(maxj+1)*(b/float(stepb)-0.5)))
      l2 = int(hg/2.0*(1-1/float(maxj+1)*(b/float(stepb)+0.5)))
      can.create_rectangle (c1,l1,c2,l2,fill=color,outline='white')
  for i in range(-4,5):
    co = int(wd/2.0*(1+1/float(maxi+1)*(i/float(stepa))))
    lo = int(hg/2.0*(1-1/float(maxj+1)*(i/float(stepb))))
    can.create_line (1, lo, wd-1, lo, fill='grey')
    can.create_line (co, 1, co, hg-1, fill='grey')
  mainloop()

def tranche():
  # nd = nq*(nq+3)
  coefc = 512
  maxi = 10
  maxj = 10
  stepa = 0.2
  stepb = 0.2
  master=Tk()
  can=Canvas(master,width=wd,height=hg,bg='white')
  can.pack(side=LEFT)
  b = Button (master, text=" ", command=btn)
  b.pack()
  # x0 = [gauss(0,1) for i in range(nd)]
  x0 = [0 for i in range(nd)]
  # x0 = vecteurqimt (qi3macd, mt3macd(12,26,9))
  u = [gauss(0,1) for i in range(nd)]
  v = [gauss(0,1) for i in range(nd)]
  w = add (v, prod(-prod(u,v)/float(prod(u,u)),u))
  un = prod (prod(u,u)**-0.5, u)
  wn = prod (prod(w,w)**-0.5, w)
  for i in range(-maxi,maxi+1):
    for j in range(-maxj,maxj+1):
      a = i*stepa
      b = j*stepb
      x = add (x0, add (prod(a,un), prod(b,wn)))
      divg=0
      for y in x:
        if y<-1 or y>1:
          divg=1
      # if divg==0:
      if 0==0:
        kd = valeur(x)
        k = kd[0]-1
        print str(a) + '\t' + str(b) + '\t' + str(k)
        # color = '#%02x%02x%02x' % (0,min(int(k*128),255),0)
        cdivg=32
        # cdivg=0
        if k < 0:
          # color = '#%02x%02x%02x' % (min(int(-k*512),255),0,0)
          color = '#%02x%02x%02x' % (255-cdivg*divg, max(0,int(255+k*coefc)),max(0,int(255+k*coefc)))
        if k == 0:
          # color = 'white'
          color = '#%02x%02x%02x' % (255-cdivg*divg, 255-cdivg*divg, 255-cdivg*divg)
        if k > 0:
          # color = '#%02x%02x%02x' % (0,min(int(k*512),255),0)
          color = '#%02x%02x%02x' % (max(0,int(255-k*coefc)),255-cdivg*divg,max(0,int(255-k*coefc)))
        # if divg==0: color='white'
        # else: color='blue'
        c1 = int(wd/2.0*(1+1/float(maxi+1)*(a/float(stepa)-0.5)))
        c2 = int(wd/2.0*(1+1/float(maxi+1)*(a/float(stepa)+0.5)))
        l1 = int(hg/2.0*(1-1/float(maxj+1)*(b/float(stepb)-0.5)))
        l2 = int(hg/2.0*(1-1/float(maxj+1)*(b/float(stepb)+0.5)))
        can.create_rectangle (c1,l1,c2,l2,fill=color,outline='grey')
  for i in range(-1,2):
    co = int(wd/2.0*(1+1/float(maxi+1)*(i/float(stepa))))
    lo = int(hg/2.0*(1-1/float(maxj+1)*(i/float(stepb))))
    can.create_line (1, lo, wd-1, lo, fill='grey')
    can.create_line (co, 1, co, hg-1, fill='grey')
  mainloop()

def correltranche():
  # nd = nq*(nq+3)
  coefc = 1024
  maxi = 16
  maxj = 16
  stepa = 0.5
  stepb = 0.5
  master=Tk()
  can=Canvas(master,width=wd,height=hg,bg='white')
  can.pack(side=LEFT)
  b = Button (master, text=" ", command=btn)
  b.pack()
  x0 = [gauss(0,1) for i in range(nd)]
  # x0 = [0 for i in range(nd)]
  # x0 = vecteurqimt (qi3macd, mt3macd(12,26,9))
  u = [gauss(0,1) for i in range(nd)]
  v = [gauss(0,1) for i in range(nd)]
  w = add (v, prod(-prod(u,v)/float(prod(u,u)),u))
  un = prod (prod(u,u)**-0.5, u)
  wn = prod (prod(w,w)**-0.5, w)
  cor=[]
  for i in range(-maxi,maxi+1):
    for j in range(-maxj,maxj+1):
      a = i*stepa
      b = j*stepb
      x = add (x0, add (prod(a,un), prod(b,wn)))
      divg=0
      for y in x:
        if y<-1 or y>1:
          divg=1
      # if divg==0:
      if 0==0:
        # kd1 = valeurv(x,'AXA')
        kd1 = valeurcv(x,coursval(cours1,'PPR'))
        k1 = kd1[0]-1
        # kd2 = valeurv(x,'PPR')
        kd2 = valeurcv(x,coursval(cours2,'AXA'))
        k2 = kd2[0]-1
        # kd3 = valeurv(x,'HERMES')
        kd3 = valeurcv(x,coursval(cours3,'ALTEN'))
        k3 = kd3[0]-1
        print str(a) + '\t' + str(b) + '\t'
        cor=cor+[[k1,k2,k3]]
        red = max(0,min(255,128+coefc*k1))
        green = max(0,min(255,128+coefc*k2))
        blue = max(0,min(255,128+coefc*k3))
        color='#%02x%02x%02x' % (red,green,blue)
        c1 = int(wd/2.0*(1+1/float(maxi+1)*(a/float(stepa)-0.5)))
        c2 = int(wd/2.0*(1+1/float(maxi+1)*(a/float(stepa)+0.5)))
        l1 = int(hg/2.0*(1-1/float(maxj+1)*(b/float(stepb)-0.5)))
        l2 = int(hg/2.0*(1-1/float(maxj+1)*(b/float(stepb)+0.5)))
        can.create_rectangle (c1,l1,c2,l2,fill=color,outline='grey')
  for i in range(-1,2):
    co = int(wd/2.0*(1+1/float(maxi+1)*(i/float(stepa))))
    lo = int(hg/2.0*(1-1/float(maxj+1)*(i/float(stepb))))
    can.create_line (1, lo, wd-1, lo, fill='grey')
    can.create_line (co, 1, co, hg-1, fill='grey')
  mainloop()
  graphxyz(cor,wd,hg)

def tranche3(lc):
  # nd = nq*(nq+3)
  coefc = 512
  maxi = 10
  maxj = 10
  stepa = 0.2
  stepb = 0.2
  master=Tk()
  can=Canvas(master,width=wd,height=hg,bg='white')
  can.pack(side=LEFT)
  b = Button (master, text=" ", command=btn)
  b.pack()
  x0 = [gauss(0,0.25) for i in range(nd)]
  # x0 = [0 for i in range(nd)]
  # x0 = vecteurqimt (qi3macd, mt3macd(12,26,9))
  u = [gauss(0,1) for i in range(nd)]
  v = [gauss(0,1) for i in range(nd)]
  w = add (v, prod(-prod(u,v)/float(prod(u,u)),u))
  un = prod (prod(u,u)**-0.5, u)
  wn = prod (prod(w,w)**-0.5, w)
  cor = []
  for i in range(-maxi,maxi+1):
    for j in range(-maxj,maxj+1):
      a = i*stepa
      b = j*stepb
      x = add (x0, add (prod(a,un), prod(b,wn)))
      divg=0
      for y in x:
        if y<-1 or y>1:
          divg=1
      if divg==0:
        lkld = valeurslc(x,lc)
        lk=lkld[0]
        cor = cor + [[lk[m]-1 for m in range(3)]]
        rgb=[max(0,min(255,128+coefc*(lk[m]-1))) for m in range(3)]
        color='#%02x%02x%02x' % (rgb[0],rgb[1],rgb[2])
        # k = kd[0]-1
        print str(a) + '\t' + str(b) + '\t' + str(lk)
        c1 = int(wd/2.0*(1+1/float(maxi+1)*(a/float(stepa)-0.5)))
        c2 = int(wd/2.0*(1+1/float(maxi+1)*(a/float(stepa)+0.5)))
        l1 = int(hg/2.0*(1-1/float(maxj+1)*(b/float(stepb)-0.5)))
        l2 = int(hg/2.0*(1-1/float(maxj+1)*(b/float(stepb)+0.5)))
        can.create_rectangle (c1,l1,c2,l2,fill=color,outline='#808080')
  for i in range(-1,2):
    co = int(wd/2.0*(1+1/float(maxi+1)*(i/float(stepa))))
    lo = int(hg/2.0*(1-1/float(maxj+1)*(i/float(stepb))))
    can.create_line (1, lo, wd-1, lo, fill='grey')
    can.create_line (co, 1, co, hg-1, fill='grey')
  mainloop()
  graphxyz(cor,wd,hg)

def correl(n):
  table = []
  for i in range(n):
    print i
    x = [uniform(-1,1) for j in range(nd)]
    lkld = valeurs(x)
    lk = lkld[0]
    lk1 = [k-1 for k in lk]
    table = table + [lk1]
  graphxyz(table,600,600)    

def correllc(n,lc):
  table=[]
  for i in range(n):
    print i
    x = [uniform(-1,1) for j in range(nd)]
    # x = [gauss(0,10) for j in range(nd)]
    lkld = valeurslc(x,lc)
    lk = lkld[0]
    lk1 = [k-1 for k in lk]
    table = table + [lk1]
    print lk1
  graphxyz(table,wd,hg)
  lka = [achat(c)/float(l0)-1 for c in lc]
  return [table,lka]

def khi2correl(tk):
  table = tk[0]
  lka = tk[1]  
  n = len(table)
  p = len(table[0])
  s = [0 for x in table[0]]
  n1 = 0
  for xy in table:
    z = 1
    eka = 1
    for i in range(p):
      if xy[i] != 0:
        z = 0
      if xy[i] != lka[i]:
        eka = 0
    if z == 0 and eka == 0:
      s = add (s, xy)
      n1 = n1 + 1
  m = prod (1/float(n1), s)
  compte = [[0,0],[0,0]]
  c = [0 for x in table[0]]
  for xy in table:
    z = 1
    eka = 1
    for i in range(p):
      if xy[i] != 0:
        z = 0
      if xy[i] != lka[i]:
        eka = 0
      if xy[i] < m[i]:
        c[i] = 0
      else:
        c[i] = 1
    if z == 0 and eka == 0:
      compte[c[0]][c[1]] = compte[c[0]][c[1]] + 1
  r = khi2 (compte)
  return [r,n,p,m,compte]

def correlmin(n,lc):
  table = []
  for i in range(n):
    print i
    x = [uniform(-1,1) for j in range(nd)]
    lkld = valeurslc(x,lc)
    lk = lkld[0]
    lk1 = [k-1 for k in lk]
    table = table + [[min(lk1[0],lk1[1]),min(lk1[2],lk1[3]),min(lk1[0],lk1[2])]]
  graphxyz(table,wd,hg)   

def correlmin3(n,lc):
  table = []
  for i in range(n):
    print i
    x = [uniform(-1,1) for j in range(nd)]
    # x = [gauss(0,10) for j in range(nd)]
    # x0 = vecteurqimt (qi3macd, mt3macd(12,26,9))
    # x1 = [gauss(0,0.1) for j in range(nd)]
    # x = add (x0, x1)
    lkld = valeurslc(x,lc)
    lk = lkld[0]
    lk1 = [k-1 for k in lk]
    table = table + [[min(lk1[0],min(lk1[1],lk1[2])),min(lk1[3],min(lk1[4],lk1[5])),min(lk1[0],lk1[3])]]
  graphxyz(table,wd,hg)    

def correlmin411(n,lc):
  table = []
  for i in range(n):
    print i
    x = [uniform(-1,1) for j in range(nd)]
    # x = [gauss(0,10) for j in range(nd)]
    # x0 = vecteurqimt (qi3macd, mt3macd(12,26,9))
    # x1 = [gauss(0,0.1) for j in range(nd)]
    # x = add (x0, x1)
    lkld = valeurslc(x,lc)
    lk = lkld[0]
    lk1 = [k-1 for k in lk]
    table = table + [[min(lk1[0],min(lk1[1],min(lk1[2],lk1[3]))),lk1[4],lk1[5]]]
  graphxyz(table,wd,hg)    

def correlmin3macd(n,lc):
  table = []
  for i in range(n):
    print i
    # x = [uniform(-1,1) for j in range(nd)]
    x0 = vecteurqimt (qi3macd, mt3macd(12,26,9))
    x1 = [gauss(0,0.1) for j in range(nd)]
    x = add (x0, x1)
    lkld = valeurslc(x,lc)
    lk = lkld[0]
    lk1 = [k-1 for k in lk]
    table = table + [[min(lk1[0],min(lk1[1],lk1[2])),min(lk1[3],min(lk1[4],lk1[5])),min(lk1[0],lk1[3])]]
  graphxyz(table,wd,hg)    

# lc1=[0,0,0,0,0,0]

# lc1[0]=coursval(lirecourslf(lnf[9:12]),'CARREFOUR')
# lc1[1]=coursval(lirecourslf(lnf[12:15]),'PPR')
# lc1[2]=coursval(lirecourslf(lnf[15:18]),'AXA')
# lc1[3]=coursval(lirecourslf(lnf[18:21]),'HERMES')

# lc1[0]=coursval(lirecourslf(lnf[0:6]),'CARREFOUR')
# lc1[1]=coursval(lirecourslf(lnf[6:12]),'PPR')
# lc1[2]=coursval(lirecourslf(lnf[12:18]),'AXA')
# lc1[3]=coursval(lirecourslf(lnf[18:24]),'HERMES')

# lnf=lnfvista

# lc1[0]=coursval(lirecourslf(lnf[0:4]),'BOUYGUES')
# lc1[3]=coursval(lirecourslf(lnf[4:8]),'RENAULT')
# lc1[1]=coursval(lirecourslf(lnf[8:12]),'CARREFOUR')
# lc1[4]=coursval(lirecourslf(lnf[12:16]),'PPR')
# lc1[5]=coursval(lirecourslf(lnf[16:20]),'AXA')
# lc1[2]=coursval(lirecourslf(lnf[20:24]),'HERMES')

def tranchetest():
  coefc = 2048
  maxi = 20
  maxj = 20
  stepa = 0.5
  stepb = 0.5
  # master=Tk()
  # can=Canvas(master,width=wd,height=hg,bg='white')
  # can.pack(side=LEFT)
  # b = Button (master, text=" ", command=btn)
  # b.pack()
  x0 = [gauss(0,1) for i in range(nd)]
  u = [gauss(0,1) for i in range(nd)]
  v = [gauss(0,1) for i in range(nd)]
  w = add (v, prod(-prod(u,v)/float(prod(u,u)),u))
  un = prod (prod(u,u)**-0.5, u)
  wn = prod (prod(w,w)**-0.5, w)
  for i in range(-maxi,maxi+1):
    for j in range(-maxj,maxj+1):
      a = i*stepa
      b = j*stepb
      x = add (x0, add (prod(a,un), prod(b,wn)))
      kd = valeur(x)
      k = kd[0]-1
      print str(a) + '\t' + str(b) + '\t' + str(k)
      # color = '#%02x%02x%02x' % (0,min(int(k*128),255),0)
      if k < 0:
        # color = '#%02x%02x%02x' % (min(int(-k*512),255),0,0)
        color = '#%02x%02x%02x' % (255, max(0,int(255+k*coefc)),max(0,int(255+k*coefc)))
      if k == 0:
        color = 'white'
      if k > 0:
        # color = '#%02x%02x%02x' % (0,min(int(k*512),255),0)
        color = '#%02x%02x%02x' % (max(0,int(255-k*coefc)),255,max(0,int(255-k*coefc)))
      c1 = int(wd/2.0*(1+1/float(maxi+1)*(a/float(stepa)-0.5)))
      c2 = int(wd/2.0*(1+1/float(maxi+1)*(a/float(stepa)+0.5)))
      l1 = int(hg/2.0*(1-1/float(maxj+1)*(b/float(stepb)-0.5)))
      l2 = int(hg/2.0*(1-1/float(maxj+1)*(b/float(stepb)+0.5)))
      # can.create_rectangle (c1,l1,c2,l2,fill=color,outline='white')
      if k>0:
        for i in range(1,len(kd)):
          courbes(kd[i],['black','green','blue'],wd2,hg,str(x))
  # mainloop()

    

