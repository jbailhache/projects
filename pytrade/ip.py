
npix = 2

def min_max_ip(cours,p):
  minip = []
  maxip = []
  for cv in cours:
    print cv[0][1]
    q = q_repete1gsc(init_indics,etape_indics,graphe_indics,cv,p)
    if minip == []:
      minip = q.minip
    else:
      for i in range(len(minip)):
        if q.minip[i]<minip[i]:
          minip[i] = q.minip[i]
    if maxip == []:
      maxip = q.maxip
    else:
      for i in range(len(maxip)):
        if q.maxip[i]>maxip[i]:
          maxip[i] = q.maxip[i]
  return [minip, maxip]

def tabs_ip (cours, p):
  [minip,maxip] = min_max_ip (cours,p)
  tab = [[0.0 for i in range(hg/npix)] for j in range(wd/npix)]
  tabh = [[0.0 for i in range(hg/npix)] for j in range(wd/npix)]
  tabb = [[0.0 for i in range(hg/npix)] for j in range(wd/npix)]  
  for cv in cours:
    print cv[0][1]
    q = q_repete1gsc (init_indics, etape_indics, graphe_indics, cv, p)
    for t in range(len(cv)):
      x = int((wd/npix-1) * (q.histip[t][0] - minip[0]) / float(maxip[0]-minip[0]))
      y = int((hg/npix-1) * (q.histip[t][1] - minip[1]) / float(maxip[1]-minip[1]))
      c = cv[t][6]
      ch = c * 1.02
      cb = c / 1.02
      tph = 0.0
      tpb = 0.0
      for u in range (t+1, len(cv)):
        th = (cv[u][6] - cv[t][6]) / cv[t][6] / (u-t)
        if th > tph: tph = th
        tb = (cv[u][6] - cv[t][6]) / cv[t][6] / (u-t)
        if tb < tpb: tpb = tb
      # print 'x=',x,' y=',y
      tab[x][y] = tab[x][y] + tph + tpb
      # tab[x][y] = 1.0
      tabh[x][y] = tabh[x][y] + tph
      tabb[x][y] = tabb[x][y] - tpb
  return [tab, tabh, tabb]

def tabsn (tabs):
  [tab,tabh,tabb]=tabs
  tabn=[]
  for l in tab:
    s = 0.0
    for x in l:
      s = s + x
    tabn = tabn + [s]
  tabhn = []
  for l in tabh:
    s = 0.0
    for x in l:
      s = s + x
    tabhn = tabhn + [s]
  tabbn = []
  for l in tabb:
    s = 0.0
    for x in l:
      s = s + x
    tabbn = tabbn + [s]
  return [tabn,tabhn,tabbn]

def graph_tabs(tabs,blanc,fh,fb):
  [tab,tabh,tabb] = tabs
  master=Tk()
  w=Canvas(master,width=wd,height=hg,bg='white')
  w.pack(side=LEFT)
  b = Button (master, text=" ", command=btn)
  b.pack()
  mi=10000.0
  ma=-10000.0
  mih=10000.0
  mah=-10000.0
  mib=10000.0
  mab=-10000.0
  for x in range(wd/npix):
    for y in range(hg/npix):
      if tab[x][y]<mi:
        mi=tab[x][y]
      if tab[x][y]>ma:
        ma=tab[x][y]
      if tabh[x][y]<mih:
        mih=tabh[x][y]
      if tabh[x][y]>mah:
        mah=tabh[x][y]
      if tabb[x][y]<mib:
        mib=tabb[x][y]
      if tabb[x][y]>mab:
        mab=tabb[x][y]
  for x in range(wd/npix):
    for y in range(hg/npix):
      z = 255 - 255 * (tab[x][y] - mi) / float (ma-mi)
      if fh:
        zh = (tabh[x][y] - mih) / float(mah-mih)
      else:
        zh = 0
      if fb:
        zb = (tabb[x][y] - mib) / float(mab-mib)
      else:
        zb = 0
      # col = '#%02x%02x%02x' % (z, z, z)
      if blanc:
        col = '#%02x%02x%02x' % (255-255*zh, 255-255*zb, 255)
      else:
        col = '#%02x%02x%02x' % (255*zb, 255*zh, 0)
      for l in range(npix):
        w.create_line (x*npix, y*npix+l, x*npix+npix, y*npix+l, fill=col)
  mainloop()
      
def graph_tabsn(tabs,blanc,fh,fb):
  [tab,tabh,tabb] = tabs
  master=Tk()
  w=Canvas(master,width=wd,height=hg,bg='white')
  w.pack(side=LEFT)
  b = Button (master, text=" ", command=btn)
  b.pack()
  mi=10000.0
  ma=-10000.0
  mih=10000.0
  mah=-10000.0
  mib=10000.0
  mab=-10000.0
  for x in range(wd/npix):
      if tab[x]<mi:
        mi=tab[x]
      if tab[x]>ma:
        ma=tab[x]
      if tabh[x]<mih:
        mih=tabh[x]
      if tabh[x]>mah:
        mah=tabh[x]
      if tabb[x]<mib:
        mib=tabb[x]
      if tabb[x]>mab:
        mab=tabb[x]
  for x in range(wd/npix):
      # y = int((hg/npix-1) * (q.histip[t][1] - minip[1]) / float(maxip[1]-minip[1]))
      y = int ( (hg/npix-1) * (tab[x] - mi) / float (ma - mi) )
      z = 255 - 255 * (tab[x] - mi) / float (ma-mi)
      if fh:
        zh = (tabh[x] - mih) / float(mah-mih)
      else:
        zh = 0
      if fb:
        zb = (tabb[x] - mib) / float(mab-mib)
      else:
        zb = 0
      # col = '#%02x%02x%02x' % (z, z, z)
      if blanc:
        col = '#%02x%02x%02x' % (255-255*zh, 255-255*zb, 255)
      else:
        col = '#%02x%02x%02x' % (255*zb, 255*zh, 0)
      print 'col=',col
      for l in range(npix):
        w.create_line (x*npix, y*npix+l, x*npix+npix, y*npix+l, fill=col)
  mainloop()
      
def acpind (cv, p):
  print 'repete1gsc'
  q = q_repete1gsc (init_indics, etape_indics, graphe_indics, cv, p)
  print 'centred'
  # data = centred(transpose(q.histind))
  data = transpose(centred(q.histind))
  print 'acp'
  [s,l,u,c] = acp (data)
  print 'graph'
  graphxy (c, wd, hg)

  
  
    

  