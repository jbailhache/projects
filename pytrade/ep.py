
def ep(intraday,t1,periode,n,tau0,tau1):
  master=Tk()
  w=Canvas(master,width=wd,height=hg)
  w.pack(side=LEFT)
  w.create_rectangle(1,1,wd-1,hg-1,fill=bgcolor)

  # intraday = format_cours_intraday (lire_isin(v))

  imin = 9*60
  imax = 18*60

  cimin = 1000000
  cimax = 0

  for i in intraday:
    if i[1]<cimin: cimin=i[1]
    if i[1]>cimax: cimax=i[1]

  premier = 1
  x = 0
  y = 0

  for i in intraday:
    xp = x
    yp = y
    x = wd * (i[0]-imin) / (imax-imin)
    y = hg - hg * (i[1]-cimin) / (cimax-cimin)
    if premier:
      premier = 0
    else:
      w.create_line (xp, yp, x, y, fill=inki)

  phi = []
  psi = []
  for o in range (n):
    tau = tau0 + (tau1 - tau0) * o / (n - 1)
    print 'tau=',tau
    phi1 = 0
    psi1 = 0
    s = 0
    for i in intraday:
      t = i[0]
      if t <= t1:
        c = i[1]
        a = math.exp(float(t-t1)/periode)
        c1 = a * c
        s = s + a
        phi1 = phi1 + c1 * math.cos (t / tau) 
        psi1 = psi1 + c1 * math.sin (t / tau) 
    phi = phi + [phi1 / s]
    psi = psi + [psi1 / s]

  premier = 1
  x = 0
  y = 0
  dmin = 1000000.0
  dmax = -1000000.0

  for t in range(imin,imax):
    d = 0
    for o in range (n):
      tau = tau0 + (tau1 - tau) * o / (n - 1)
      d = d + phi[o] * math.cos (t / tau) + psi[o] * math.sin (t / tau)
    d = d / n
    if d < dmin:
      dmin = d
    if d > dmax:
      dmax = d

  for t in range(imin,imax):
    xp = x
    yp = y
    d = 0
    for o in range (n):
      tau = tau0 + (tau1 - tau) * o / (n - 1)
      d = d + phi[o] * math.cos (t / tau) + psi[o] * math.sin (t / tau)
    d = d / n 
    x = wd * (t - imin) / (imax - imin)
    y = hg - hg * (d - dmin) / (dmax - dmin)
    if premier:
      premier = 0
    else:
      print 't=', t, ' d=', d, ' xp=', xp, ' yp=', yp, ' x=', x, ' y=', y
      w.create_line (xp, yp, x, y, fill='green')

  print 'mainloop'

  mainloop()


