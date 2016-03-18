
pi = 3.1415926

def cid(v):
  return format_cours_intraday (lire_isin(v))

def epf(intraday,t1,n,tau0,tau1):
  ept(intraday,1,1,0,t1,1,n,tau0,tau1)

def ept(intraday,a,b,tr,t1,periode,n,tau0,tau1):
  master=Tk()
  w=Canvas(master,width=wd,height=hg)
  w.pack(side=LEFT)
  w.create_rectangle(1,1,wd-1,hg-1,fill=bgcolor)

  # intraday = format_cours_intraday (lire_isin(v))

  l0 = math.log(tau0)
  l1 = math.log(tau1)

  imin = 9*60
  imax = 18*60

  cimin = 1000000
  cimax = 0

  for i in intraday:
    if i[1]<cimin: cimin=i[1]
    if i[1]>cimax: cimax=i[1]

  cimin1 = 1000000
  cimax1 = 0

  for i in intraday:
    if i[0] < t1 :
      if i[1]<cimin1: cimin1=i[1]
      if i[1]>cimax1: cimax1=i[1]

  cimoy = (cimin+cimax)/2

  x = wd * (t1 - imin) / (imax - imin)
  w.create_line (x, 1, x, hg-1, fill='red')

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

  ft = intraday[0][0]
  fc = intraday[0][1]
  
  phi = []
  psi = []
  for o in range (n):
    # tau = tau0 + (tau1 - tau0) * o / (n - 1)
    l = l0 + (l1 - l0) * o / (n - 1)
    tau = math.exp(l)
    # print 'tau=',tau
    phi1 = 0
    psi1 = 0
    s = 0
    for j in range(1,len(intraday)-1):
      i = intraday[j]
      t = i[0] 
      tp = intraday[j-1][0] 
      ts = intraday[j+1][0] 
      if t <= t1:
        lt = i[0]
        lc = i[1]
        c = i[1] - cimoy
        e = math.exp(float(t-t1)/periode)
        c1 = e * c
        s = s + e
        # phi1 = phi1 + c1 * math.cos (t / tau) 
        # psi1 = psi1 + c1 * math.sin (t / tau) 
        phi1 = phi1 + c * math.cos ((t-tr) / tau) * (ts-tp)/2
        psi1 = psi1 + c * math.sin ((t-tr) / tau) * (ts-tp)/2 

    # print 'tau=', tau, 'phi1=', phi1, 'psi1=', psi1

    phi = phi + [phi1]
    psi = psi + [psi1]

  premier = 1
  x = 0
  y = 0
  dmin = 1000000.0
  dmax = -1000000.0
  dmin1 = 1000000.0
  dmax1 = -1000000.0

  for t in range(imin,imax):
    d = 0
    for o in range (n):
      # tau = tau0 + (tau1 - tau) * o / (n - 1)
      l = l0 + (l1 - l0) * o / (n - 1)
      tau = math.exp(l)
      # d = d + phi[o] * math.cos (t / tau) + psi[o] * math.sin (t / tau) 
      # d = d + 1.0/(tau*tau) * (a * phi[o] * math.cos((t-tr)/tau) + b * psi[o] * math.sin((t-tr)/tau))
      # d = d + 1.0/(tau*tau) * (a * phi[o] * math.cos((t-tr)/tau) + b * psi[o] * math.sin((t-tr)/tau))
      d = d + 1.0/tau * (a * phi[o] * math.cos((t-tr)/tau) + b * psi[o] * math.sin((t-tr)/tau))
      # d = d + 1.0/tau * (phi[o] * math.cos(t/tau) + psi[o] * math.sin(t/tau))
      # print 'tau=', tau, ' d=', d
    # d = d / n 
    # d = 1/(2*3.1415926) * (tau1-tau0)/(n-1) * d
    # print 'd=', d
    if d < dmin:
      dmin = d
    if d > dmax:
      dmax = d
    if t < t1:
      if d < dmin1:
        dmin1 = d
      if d > dmax1:
        dmax1 = d

  print 'cimin1=', cimin1, ' cimax1=', cimax1, ' dmin1=', dmin1, ' dmax1=', dmax1

  # t = ft
  # fd = 1.0/(tau*tau) * (a * phi[o] * math.cos((t-tr)/tau) + b * psi[o] * math.sin((t-tr)/tau))

  # t = lt
  # ld = 1.0/(tau*tau) * (a * phi[o] * math.cos((t-tr)/tau) + b * psi[o] * math.sin((t-tr)/tau))

  # dmin = fd + (cimin - fc) * (ld - fd) / float(lc - fc)
  # dmax = fd + (cimax - fc) * (ld - fd) / float(lc - fc) 
  
  # print 'ft=', ft, ' lt=', lt, ' fc=', fc, ' lc=', lc, ' fd=', fd, ' ld=', ld, ' cimin=', cimin, ' cimax=', cimax, ' dmin=', dmin, ' dmax=', dmax

  dmin = dmin1 + (cimin - cimin1) * (dmax1 - dmin1) / float(cimax1 - cimin1)
  dmax = dmin1 + (cimax - cimin1) * (dmax1 - dmin1) / float(cimax1 - cimin1)

  for t in range(imin,imax):
    xp = x
    yp = y
    d = 0
    for o in range (n):
      # tau = tau0 + (tau1 - tau) * o / (n - 1)
      l = l0 + (l1 - l0) * o / (n - 1)
      tau = math.exp(l)
      # d = d + phi[o] * math.cos (t / tau) + psi[o] * math.sin (t / tau) 
      # d = d + 1.0/(tau*tau) * (a * phi[o] * math.cos((t-tr)/tau) + b * psi[o] * math.sin((t-tr)/tau))
      # d = d + 1.0/(tau*tau) * (a * phi[o] * math.cos((t-tr)/tau) + b * psi[o] * math.sin((t-tr)/tau))
      d = d + 1.0/tau * (a * phi[o] * math.cos((t-tr)/tau) + b * psi[o] * math.sin((t-tr)/tau))
      # d = d + 1.0/tau * (phi[o] * math.cos(t/tau) + psi[o] * math.sin(t/tau))
    # d = d / n 
    # d = 1/(2*3.1415926) * (tau1-tau0)/(n-1) * d
    # print 'd=', d
    x = wd * (t - imin) / (imax - imin)
    y = hg - hg * (d - dmin) / float(dmax - dmin)
    if premier:
      premier = 0
    else:
      # print 't=', t, ' d=', d, ' xp=', xp, ' yp=', yp, ' x=', x, ' y=', y
      w.create_line (xp, yp, x, y, fill='green')

  print 'mainloop'

  mainloop()


