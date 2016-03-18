
def lfc(nf):
  lcs=lirecours1(nf)[0]
  n=len(lcs)
  return lcs
 
def calcul(p,a,b,g):
  n=len(lcs)
  d=[]
  f = open ('hermes-out.txt', 'w')
  nt=0
  l=1000
  c=lcs[0][6]
  v=0
  vp=0
  k = l + nt * c
  # print k
  # for cs in lcs:
  for i in range(int(a*n),int(b*n)):
    nump=i
    cs=lcs[i]
    cp=c
    c=cs[6]
    vp=v
    v=c-cp
    if vp<0:
      if v<0:
        if v-vp<0: cas=0
        else: cas=1
      else:
        if v+vp<0: cas=2
        else: cas=3
    else:
      if v<0:
        if v+vp<0: cas=4
        else: cas=5
      else:
        if v-vp<0: cas=6
        else: cas=7
    acte1=p[cas] 
    br = vp<0 and v<0 and v>vp
    hr = vp>0 and v>0 and v<vp
    bb = vp>0 and v<0 and v+vp<0
    hb = vp<0 and v>0 and v+vp>0
    # acte1 = int(br) - int(hr) + int(bb) - int(hb)
    if acte1<0:
      acte=-nt
    elif acte1>0:
      acte=int(l/c)
    else:
      acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    f.write(str(c) + '\t' + str(nt) + '\t' + str(l) + '\t' + str(k) + '\t' + str(br) + '\t' + str(hr) + '\t' + str(bb) + '\t' + str(hb) + '\t' + str(acte) + '\n')
    d=d+[[c*10,k]]
  # print k
  f.close()
  # if k>1000:
  if g>0:
    courbes(d,['red','blue'],300,160,str(k)+' '+str(nump)+' '+str(p))
  return k

def meilleur():
  r=[0 for i in range(8)]
  r1=[0 for i in range(8)]
  lp=comb([-1,1],8)
  mk=0
  m=-1
  l=[]
  for i in range(len(lp)):
    k=calcul(lp[i],0,0.5,0)
    k1=0
    for j in range(8):
      r[j]=r[j]+lp[i][j]*(k-1000)
      if k>1000:
        r1[j]=r1[j]+lp[i][j]*(k-1000)
        k1=calcul(0,lp[i],1,0)
        l=l+[k1]
    print str(i)+'/'+str(len(lp))+' '+str(k)+' '+str(k1)+' '+str(lp[i])
    if k>mk:
      mk=k
      mp=lp[i]
      m=i 
  return [mp,mk,l,r,r1]

def correl():
  lp=comb([-1,1],8)
  c=[]
  for i in range(len(lp)):
    k1=calcul(lp[i],0,0.5,0)
    k2=calcul(lp[i],0.5,1,0)
    c=c+[[k1-1000,k2-1000]]
    print str(i)+' '+str(k1)+' '+str(k2)+' '+str(lp[i])
  return c

def detdir():
  r=[0 for i in range(8)]
  n=len(lcs)
  for i in range(0,n-3):
    c1=lcs[i][6]
    c2=lcs[i+1][6]
    c3=lcs[i+2][6]
    c4=lcs[i+3][6]
    vp=c2-c1
    v=c3-c2
    vs=c4-c3
    if vp<0:
      if v<0:
        if v-vp<0: cas=0
        else: cas=1
      else:
        if v+vp<0: cas=2
        else: cas=3
    else:
      if v<0:
        if v+vp<0: cas=4
        else: cas=5
      else:
        if v-vp<0: cas=6
        else: cas=7
    r[cas]=r[cas]+vs
  return r

def detdirn():
  n=len(lcs)
  tv=[]
  for i in range(0,n-3):
    c1=lcs[i][6]
    c2=lcs[i+1][6]
    c3=lcs[i+2][6]
    c4=lcs[i+3][6]
    vp=c2-c1
    v=c3-c2
    vs=c4-c3
    tv=tv+[[vp,v,vs]]
  return tv

def tabstat():
  r=[[0,0] for i in range(8)]
  n=len(lcs)
  for i in range(0,n-3):
    c1=lcs[i][6]
    c2=lcs[i+1][6]
    c3=lcs[i+2][6]
    c4=lcs[i+3][6]
    vp=c2-c1
    v=c3-c2
    vs=c4-c3
    if vp<0:
      if v<0:
        if v-vp<0: cas=0
        else: cas=1
      else:
        if v+vp<0: cas=2
        else: cas=3
    else:
      if v<0:
        if v+vp<0: cas=4
        else: cas=5
      else:
        if v-vp<0: cas=6
        else: cas=7
    if vs<0:
      r[cas][0]=r[cas][0]+1
    else:
      r[cas][1]=r[cas][1]+1
  return r

def khi2(t):
  nl=len(t)
  nc=len(t[0])
  sl=[0 for i in range(nl)]
  sc=[0 for j in range(nc)]
  s = 0
  for i in range(nl):
    for j in range(nc):
      sl[i] = sl[i] + t[i][j]
      sc[j] = sc[j] + t[i][j]
      s = s + t[i][j]
  # print sl
  # print sc
  # print s
  k = 0
  for i in range(nl):
    for j in range(nc):
      e = sl[i] * sc[j] / float(s) 
      # print e
      k = k + ((t[i][j] - e) ** 2) / float(e)
  return k

# t1 = [[50,70,110,60],[60,75,100,50]]


    

  
