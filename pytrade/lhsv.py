import urllib
import time
import datetime
import os

def myfloat(z1):
  z=''
  for c in z1:
    if ord(c)<128:
      z=z+c
  # print 'z='+z+'.'
  if z[0]=='-':
    return 0
  else:
    return float(z.replace(',' ,'')) 


def lire_hist_isin(isin):
  today=datetime.date.today()
  since=today+datetime.timedelta(days=-365)
  l1=time.localtime(time.mktime(since.timetuple()))
  l2=time.localtime(time.mktime(today.timetuple()))
  # print 'l1=',l1,l1[2]
  j1="%02d"%l1[2]
  m1="%02d"%l1[1]
  a1="%02d"%l1[0]
  d1=j1+'/'+m1+'/'+a1
  j2="%02d"%l2[2]
  m2="%02d"%l2[1]
  a2="%02d"%l2[0]
  d2=j2+'/'+m2+'/'+a2
  url = 'http://www.euronext.com/tools/datacentre/dataCentreDownloadExcell.jcsv?lan=FR&cha=2593&fileFormat=txt&separator=.&dateFormat=dd/MM/yy&isinCode='+isin+'&selectedMep=1&indexCompo=&opening=on&high=on&low=on&closing=on&volume=on&dateFrom='+d1+'&dateTo='+d2+'&typeDownload=2'
  page = urllib.urlopen(url)
  texte = page.read()
  return texte

def lire_hist_isin_jours(isin,j1,j2):
  today=datetime.date.today()
  since=today+datetime.timedelta(days=j1)
  to=today+datetime.timedelta(days=j2)
  l1=time.localtime(time.mktime(since.timetuple()))
  l2=time.localtime(time.mktime(to.timetuple()))
  # print 'l1=',l1,l1[2]
  # print l1
  # print l2
  j1="%02d"%l1[2]
  m1="%02d"%l1[1]
  a1="%02d"%l1[0]
  d1=j1+'/'+m1+'/'+a1
  j2="%02d"%l2[2]
  m2="%02d"%l2[1]
  a2="%02d"%l2[0]
  d2=j2+'/'+m2+'/'+a2
  url = 'http://www.euronext.com/tools/datacentre/dataCentreDownloadExcell.jcsv?lan=FR&cha=2593&fileFormat=txt&separator=.&dateFormat=dd/MM/yy&isinCode='+isin+'&selectedMep=1&indexCompo=&opening=on&high=on&low=on&closing=on&volume=on&dateFrom='+d1+'&dateTo='+d2+'&typeDownload=2'
  page = urllib.urlopen(url)
  texte = page.read()
  return texte

def nom_isin(isin):
  for x in srd:
    if x[0]==isin:
      return x[1]
  return isin

def isin_nom(nom):
  for x in srd:
    # if x[1]==nom:
    if x[1].find(nom)==0:
      return x[0]
  return nom

def cours_isin(isin):
  t=lire_hist_isin(isin)
  nom=nom_isin(isin)
  l1=t.split('\n')
  l=l1[6:len(l1)-1]
  # lcs=[[isin,nom]+[float(y) for y in x.split(';')] for x in l]
  lcs=[]
  for x in l:
    y=x.split(';')
    lcs=lcs+[[isin,nom,x[0]]+[myfloat(z) for z in y[1:len(y)]]]
  return lcs

def cours_isin_jours_1(isin,j1,j2):
  t=lire_hist_isin_jours(isin,j1,j2)
  # nom=nom_isin(isin)
  l1=t.split('\n')
  infos = l1[3].split(';') 
  nom = infos[0]
  l=l1[6:len(l1)-1]
  # lcs=[[isin,nom]+[myfloat(y) for y in x.split(';')] for x in l]
  lcs=[]
  for x in l:
    y=x.split(';')
    lcs=lcs+[[isin,nom,y[0]]+[myfloat(z) for z in y[1:len(y)]]]
  return lcs

def cours_isin_jours(isin,j1,j2):
  global tableau_cours
  print 'j1=',j1,' j2=',j2
  fn = 'cours_' + isin + '.txt'
  # print fn
  if (os.path.isfile(fn)):
    f = open(fn,'r')
    s = f.read()
    f.close()
    cf = eval(s)
    today=datetime.date.today()
    ds1=cf[0][2]
    da1=ds1.split('/')
    d1=datetime.date(int(da1[2])+2000,int(da1[1]),int(da1[0]))
    k1=(d1-today).days
    # print 'k1=',k1
    ds2=cf[len(cf)-1][2]
    da2=ds2.split('/')
    d2=datetime.date(int(da2[2])+2000,int(da2[1]),int(da2[0]))
    k2=(d2-today).days
    print 'j1=',j1,' j2=',j2,' k1=',k1,' k2=',k2
    if (k1 > j1):
      # print 'j1=',j1
      cp = cours_isin_jours_1(isin,j1,k1-1)
      # print 'cp=',cp
    else:
      cp = []
    if (k2 < j2):
      cs = cours_isin_jours_1(isin,k2+1,j2)
    else:
      cs = []
    c = cp + cf + cs
    date_debut = today+datetime.timedelta(days=j1)
    # print 'date_debut=',date_debut
    date_fin = today+datetime.timedelta(days=j2)
    # print 'date_fin=',date_fin
    indice_debut=0
    for i in range(len(c)):
      x = c[i]
      dsx=x[2]
      dax=dsx.split('/')
      dx=datetime.date(int(dax[2])+2000,int(dax[1]),int(dax[0]))
      # print 'i=',i,' dx=',dx
      if (dx-date_debut).days <= 0:
       indice_debut = i
      if (dx-date_fin).days <= 0:
       indice_fin = i
    # print 'indice_debut=',indice_debut
    # print 'indice_fin=',indice_fin
    r = c[indice_debut:indice_fin]
  else:
    c = cours_isin_jours_1(isin,j1,j2)
    r = c
  f = open (fn, 'w')
  f.write(str(c))
  f.close()
  return r
  
def cours_nom(nom):
  return cours_isin(isin_nom(nom))

def cours_nom_jours(nom,j1,j2):
  print 'cours_nom_jours: j1=',j1,' j2=',j2
  return cours_isin_jours(isin_nom(nom),j1,j2)







