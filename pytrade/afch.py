
def datestr(s):
  t = s.split('/')
  return datetime.date(int(t[2]),int(t[1]),int(t[0]))
 
def min_hms(hms):
  t = hms.split(':')
  return int(t[0])*60 + int(t[1])
	
def format_cours_hist(cv):
  # print 'cv=', cv
  if cv==[]:
    return ['',1,[]]
  debut = datestr(cv[0][2])
  today = datestr(datetime.date.today().strftime('%d/%m/%y'))
  dj = (today-debut).days
  c = []
  for x in cv:
    d = datestr(x[2])
    dif = (d-debut).days
    c = c + [[dif] + x[3:8]]
  nom = cv[0][1]
  return [nom,dj,c]

def format_cours_intraday(s):
  c = []
  lignes = s.split('\n')
  lignes = lignes[6:len(lignes)]
  for l in lignes:
    t = l.split(';')
    # print 'l=',l,' t=',t
    if len(t)==4:
      c = [ [min_hms(t[0]), myfloat(t[2].replace(',','.')), myfloat(t[3].replace(',','.'))] ] + c
  return c

lvg=[]
v=-1
j1g=-365
j2g=0

bgcolor='black'
inkc='yellow'
inkch='green'
inkcb='red'
inkh='blue'
inki = 'orange'
inkz='grey'

flag=0

def depl_afch(d):
  global v,lvg,j1g,j2g,w
  # print 'v=',v,' lvg=',lvg
  if v+d>=0 and v+d<len(lvg):
    v=v+d
  print ' lvg[',v,']=',lvg[v]
  
  l['text'] = lvg[v][0]
  
  if len(lvg[v])>=7:
    if lvg[v][4]==0:
      g=0
    else:
      g=100*lvg[v][6]/lvg[v][5]
    linf['text'] = 'A=' + '%5.2f'%lvg[v][3] + ' V=' + '%5.2f'%lvg[v][4] + ' D=' + '%4.1f'%lvg[v][5] + ' EL=' + '%5.2f'%lvg[v][6] + ' G=' + '%5.1f'%g
    
  w.create_rectangle(1,1,wd-1,hg/2,fill=bgcolor)
  w.create_rectangle(1,hg/2,wd-1,hg,fill=bgcolor)
  # print 'j1g=', j1g, ' j2g=', j2g
  # infos = format_infos_isin (lvg[v][0])
  infos = []
  
  hist1 = cours_nom_jours (lvg[v][0], j1g, j2g)
  [nom,dj,hist] = format_cours_hist (hist1)
  # print 'dj=',dj
  lnom['text']=nom
  if len(hist1)==0:
    ldates['text']='---'
  else:
    ldates['text'] = hist1[0][2] + ' - ' + hist1[len(hist1)-1][2]
  
  coef = 0
  djm = 0
  signe = 0
  # print 'infos=', infos
  if infos == []:
    type = ''
    ex = 0
    sj = ''
    matur = 0
  else:
   try:
    # print '*** infos=',infos
    type = infos[6]
    if type == 'Call':
      coef = 1/float(lvg[v][1])
      signe=1
    elif type=='Put':
      coef = -1/float(lvg[v][1])
      signe=-1
    else:
      coef=0
      signe=0
    ex = float(infos[7])
    sj = infos[33]
    # print 'infos[8]=<'+infos[8]+'>'
    matur = infos[8]
    print 'matur=',matur
    if matur=='-':
      djm=0
    else:
      matur = datestr(datestr(infos[8]).strftime('%d/%m/%y'))
      today = datestr(datetime.date.today().strftime('%d/%m/%y'))
      djm = (matur-today).days
      x = wd/2 + wd/2 * djm / float(dj)
      w.create_line (x, 1, x, hg-1, fill='brown')
   except:
    type = ''
    ex = 0
    sj = ''
    matur = 0
  print 'sj=',sj,' type=',type,' coef=',coef,' ex=',ex,' matur=',matur,' djm=',djm
  
  # histsj1 = cours_nom_jours (sj, -dj, 0)
  # [nomsj,djsj,histsj] = format_cours_hist (histsj1)

  # print 'histsj=',histsj
  # if histsj!=[]:
  #   p = (histsj[0][4] - ex) / hist[0][4]
  #   print 'p=',p

  # intraday = format_cours_intraday (lire_euronext(lvg[v][0]))

  hmin = 0
  # hmax = hist[len(hist)-1][0]
  hmax = dj
  imin = 9*60
  imax = 18*60
  chmin = 1000000
  chmax = 0
  cimin = 1000000
  cimax = 0
  for h in hist:
    if h[3]<chmin: chmin=h[3]
    if h[2]>chmax: chmax=h[2]
  # for i in intraday:
  #  if i[1]<cimin: cimin=i[1]
  #  if i[1]>cimax: cimax=i[1]
    
  # if flag:
  #  for h in histsj:
  #    vih = coef * (h[2] - ex)
  #    if vih>chmax: chmax=vih
  #    vib = coef * (h[3] - ex)
  #    if vib<chmin: chmin=vib
    
  # lmax['text']=chmax
  # lmin['text']=chmin
  # lmaxid['text']=cimax
  # lminid['text']=cimin
  # if len(intraday)==0:
  #   last=0
  # else:
  #   last = intraday[len(intraday)-1][1]
  last = hist[len(hist)-1][4]

  # llast['text']=last
  lmax['text']=str(chmin)+' '+str(chmax)
  llast['text']=str(cimin)+' '+str(last)+' '+str(cimax)

  if len(lvg[v])>3:
    achat = lvg[v][3]
    vente = lvg[v][4]
  else:
    achat = last
    vente = last
    
  if achat>chmax: chmax=achat
  if achat<chmin: chmin=achat
  if vente>chmax: chmax=vente
  if vente<chmin: chmin=vente
      
  if chmax==chmin:
    chmin=chmin-1
    chmax=chmax+1
    
  cw=last
  par=lvg[v][1]
  # if len(histsj)>0:
  #   csj=histsj[len(histsj)-1][4]
  # else:
  #   csj=0
  csj=0
    
  # print ' lvg=',lvg,' signe=',signe,' par=',par,' cw=',cw
  pm=ex+signe*par*cw
  if csj==0:
    pr=0
  else:
    pr=signe*(pm/csj-1)
  if djm==0:
    tp=0
  else:
    # tp=pr/float(djm)
    tp=(1+pr)**(1/float(djm))-1
  if cw*par == 0:
    levier=0
  else:
    levier=csj/(cw*par)
  
  lind['text']='PM='+str(pm)+' PR='+'%3.1f'%(100*pr)+' TP='+'%4.2f'%(100*tp)+' G='+'%3.1f'%levier

  y = hg - hg * (last-chmin) / (chmax-chmin)
  w.create_line (1, y, wd-1, y, fill=inkz)
  # w.create_line (wd/2, 1, wd/2, hg-1, fill=inkz)
  
  ya = hg - hg * (achat-chmin) / (chmax-chmin)
  yv = hg - hg * (vente-chmin) / (chmax-chmin)
  w.create_line (1, ya, wd-1, ya, fill='darkgreen')
  w.create_line (1, yv, wd-1, yv, fill='darkred')
  
  premier = 1
  x = 0
  y = 0
  
    
  
  premier = 1
  x = 0
  yc = 0
  for h in hist:
    xp = x
    yp = yc
    # x = wd/2 * h[0] / hmax
    x = wd * h[0] / hmax
    yo = hg - hg * (h[1]-chmin) / (chmax-chmin)
    yh = hg - hg * (h[2]-chmin) / (chmax-chmin)
    yb = hg - hg * (h[3]-chmin) / (chmax-chmin)
    yc = hg - hg * (h[4]-chmin) / (chmax-chmin)
    
    if premier:
      premier = 0
    else:
      w.create_line (xp, yp, x, yo, fill=inkh)
    if h[4]>h[1]:
      col = inkch
    elif h[4]<h[1]:
      col = inkcb
    else:
      col=inkc
    w.create_line (x, yb, x, yh, fill=col)
    w.create_line (x, yo, x-2, yo, fill=col)
    w.create_line (x, yc, x+2, yc, fill=col)
  premier = 1
  x = 0
  y = 0  
  # for i in intraday:
  #  xp = x
  #  yp = y
  #  x = wd/2 + wd/2 * (i[0]-imin) / (imax-imin)
  #  y = hg - hg * (i[1]-chmin) / (chmax-chmin)
  #  if premier:
  #    premier = 0
  #  else:
  #    w.create_line (xp, yp, x, y, fill=inki)

def prec_afch():
  depl_afch(-1)

def suivant_afch():
  depl_afch(1)

def afch(lv,j1,j2):
  global w,l,lnom,linf,lind,ldates,lmax,lmin,lmaxid,llast,lminid,bp,b,v,c,lnj,lvg,j1g,j2g
  if type(lv[0])==type('a'):
    lvg=[[x,1] for x in lv]
  else:
    lvg=lv
  j1g=j1
  j2g=j2
  v=-1
  master=Tk()
  w=Canvas(master,width=wd,height=hg)
  w.pack(side=LEFT)
  w.create_rectangle(1,1,wd-1,hg-1,fill=bgcolor)
  l=Label(master,text="")
  l.pack()
  lnom=Label(master,text="")
  lnom.pack()
  linf=Label(master,text="")
  linf.pack()
  lind=Label(master,text="")
  lind.pack()
  ldates=Label(master,text="")
  ldates.pack()
  lmax=Label(master,text="")
  lmax.pack()
  # lmin=Label(master,text="")
  # lmin.pack()
  # lnj = Label(master,text="")
  # lnj.pack()
  # lmaxid=Label(master,text="")
  # lmaxid.pack()
  llast = Label(master,text="")
  llast.pack()
  # lminid=Label(master,text="")
  # lminid.pack()
  bp=Button(master,text="Precedent",command=prec_afch)
  bp.pack()
  b = Button (master, text="Suivant", command=suivant_afch)
  b.pack()
  v=-1
  mainloop()


    
