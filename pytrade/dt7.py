
import math

def clt(t):
  return [[10*60+i*30-t,10*60+i*30] for i in range(16)]

def tracer (tp, cp, t, c, couleur, g):
  global imin, imax, cimin, cimax, premier, w
  if g:  
    xp = wd * (tp-imin) / (imax-imin)
    yp = hg - hg * (cp-cimin) / (cimax-cimin)
    x = wd * (t-imin) / (imax-imin)
    y = hg - hg * (c-cimin) / (cimax-cimin)
    if premier:
      premier = 0
    else:
      w.create_line (xp, yp, x, y, fill=couleur)

# def dt (cid, tau1, tau2, tau3, seuil, lt, g):
def dt (cid, indic, lt, seuil, tau1, tau2, tau3, g):

  global imin, imax, cimin, cimax, premier, w

  if g:
    master=Tk()
    w=Canvas(master,width=wd,height=hg)
    w.pack(side=LEFT)
    w.create_rectangle(1,1,wd-1,hg-1,fill=bgcolor)

    x = wd * (lt[0][0] - imin) / (imax - imin)
    w.create_line (x, 1, x, hg-1, fill='red')

    x = wd * (lt[0][1] - imin) / (imax - imin)
    w.create_line (x, 1, x, hg-1, fill='red')

  imin = 8*60
  imax = 19*60

  cimin = 1000000
  cimax = 0

  for ct in cid:
    if ct[1]<cimin: cimin=ct[1]
    if ct[1]>cimax: cimax=ct[1]

  premier = 1
  x = 0
  y = 0

  t = 9*60
  c = cid[0][1]
  
  a1 = c
  b1 = 1
  mme1 = a1/b1
  
  a2 = c
  b2 = 1
  mme2 = a2/b2
  
  macd = 0

  a3 = 0
  b3 = 1
  mme3 = a3/b3
  
  ca = [0 for i in range(len(lt))]
  typ = ['none' for i in range(len(lt))]
  ng = 0
  np = 0
  nn = 0

  for ct in cid:

    xp = x
    yp = y
    tp = t
    cp = c
    t = ct[0]
    c = ct[1]
    a1p = a1
    b1p = b1
    mme1p = mme1
    a2p = a2
    b2p = b2
    mme2p = mme2
    a3p = a3
    b3p = b3
    macdp = macd 
    mme3p = mme3 
    
    # print 'mme3=', mme3

    for i in range(len(lt)):
      if t>lt[i][0] and t<lt[i][1] and ca[i]==0:

        if indic=='mme':
          if cp / mme1p > 1 + seuil:
            typ[i] = 'up'
            ca[i] = cp
          elif cp / mme1p < 1 - seuil:
            typ[i] = 'down'
            ca[i] = cp

        elif indic=='macd':
          if macd / mme3 > 1 + seuil:
            typ[i] = 'up'
            ca[i] = cp
          elif macd / mme3 < 1 - seuil:
            typ[i] = 'down'
            ca[i] = cp

        else:
          print 'indicateur inconnu: ', indic

      if t>lt[i][1] and ca[i]!=0:
        if typ[i] == 'up':
          if cp > ca[i]:
            # print i, ' gagne'
            ng = ng + 1
          elif cp < ca[i]:
            # print i, ' perdu'
            np = np + 1
          else:
            # print i, ' nul'
            nn = nn + 1
        elif typ[i] == 'down':
          if cp > ca[i]:
            # print i, ' perdu'
            np = np + 1
          elif cp < ca[i]:
            # print i, ' gagne'
            ng = ng + 1
          else:
            # print i, ' nul'
            nn = nn + 1
        ca[i] = 0

    tracer (tp, cp, t, c, 'orange', g)
    
    e1 = math.exp (float(tp-t)/tau1) 
    a1 = a1p * e1 + c
    b1 = b1p * e1 + 1
    mme1 = a1/ b1
    tracer (tp, mme1p, t, mme1, 'green', g)
    
    e2 = math.exp (float(tp-t)/tau2)
    a2 = a2p * e2 + c
    b2 = b2p * e2 + 1
    mme2 = a2/b2
    tracer (tp, mme2p, t, mme2, 'blue', g)
    
    macd = mme2 - mme1 
    e3 = math.exp (float(tp-t)/tau3)
    a3 = a3p * e3 + macd 
    b3 = b3p * e3 + 1
    mme3 = a3/b3
    
  if g:
    print 'gagne: ', ng, ' perdu: ', np, ' nul: ', nn

  if g:
    mainloop()

  return [ng, np, nn]

def dtlp (cid, indic, lp):
  return dt (cid, indic, clt(lp[0]), lp[1], lp[2], lp[3], lp[4], 0)

def meilleure_lp_mme (cid, n, lpmin, lpmax):
  r = 0.75
  mgain = -10000
  mtaux = 0.0
  mgpn = []
  mlp = []
  for i0 in range(n):
    p0 = lpmin[0] * ((lpmax[0] / float(lpmin[0])) ** (i0/float(n-1)))
    for i1 in range(n):
      p1 = lpmin[1] * ((lpmax[1] / float(lpmin[1])) ** (i1/float(n-1)))
      for i2 in range(n):
        p2 = lpmin[2] * ((lpmax[2] / float(lpmin[2])) ** (i2/float(n-1)))
        lp = [p0, p1, p2, 1, 1]
        gpn = dtlp (cid, 'mme', lp)
        if gpn[0] == 0:
          taux = 0
        else:
          taux = gpn[0] / float (gpn[0] + gpn[1])
        gain = gpn[0] * r - gpn[1]
        if gain > mgain :
          mgain = gain 
          mtaux = taux
          mlp = lp
          mgpn = gpn
  return mlp

def meilleure_lp_macd (cid, n, lpmin, lpmax):
  r = 0.75
  mgain = -10000
  mtaux = 0.0
  mgpn = []
  mlp = []
  
  for i0 in range(n):
    p0 = lpmin[0] * ((lpmax[0] / float(lpmin[0])) ** (i0/float(n-1)))
    for i1 in range(n):
      p1 = lpmin[1] * ((lpmax[1] / float(lpmin[1])) ** (i1/float(n-1)))
      for i2 in range(n):
        p2 = lpmin[2] * ((lpmax[2] / float(lpmin[2])) ** (i2/float(n-1)))
        for i3 in range(n):
          p3 = lpmin[3] * ((lpmax[3] / float(lpmin[3])) ** (i3/float(n-1)))
          for i4 in range(n):
            p4 = lpmin[4] * ((lpmax[4] / float(lpmin[4])) ** (i4/float(n-1)))
            
            lp = [p0, p1, p2, p3, p4]
            gpn = dtlp (cid, 'macd', lp)
            if gpn[0] == 0:
              taux = 0
            else:
              taux = gpn[0] / float (gpn[0] + gpn[1])
            gain = gpn[0] * r - gpn[1]
            if gain > mgain :
              mgain = gain
              mtaux = taux
              mlp = lp
              mgpn = gpn

  return mlp

      





    
