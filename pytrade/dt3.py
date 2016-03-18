
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

def dt (cid, tau, seuil, lt, g):

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
  a = cid[0][1]
  b = 1
  c = cid[0][1]
  mme = a/b

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
    ap = a
    bp = b
    mmep = mme
    
    for i in range(len(lt)):
      if t>lt[i][0] and t<lt[i][1] and ca[i]==0:
        # if cp > mmep:
        if cp / mmep > 1 + seuil:
          typ[i] = 'up'
          ca[i] = cp
        # elif cp < mmep:
        elif cp / mmep < 1 - seuil:
          typ[i] = 'down'
          ca[i] = cp
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
    
    e = math.exp (float(tp-t)/tau) 
    a = ap * e + c
    b = bp * e + 1
    mme = a / b
    tracer (tp, mmep, t, mme, 'green', g)

  print 'gagne: ', ng, ' perdu: ', np, ' nul: ', nn

  if g:
    mainloop()

  return [ng, np, nn]



    
