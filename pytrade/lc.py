import urllib
from Tkinter import *

def float1(s):
 t=''
 for c in s:
  if c==',':
   t=t+'.'
  if ord(c)>=ord('0') and ord(c)<=ord('9'):
   t=t+c
 return float(t)

def lire_isin(isin):
  url = 'http://www.euronext.com/tools/datacentre/dataCentreDownloadExcell.jcsv?lan=FR&cha=2593&fileFormat=txt&separator=,&dateFormat=dd/MM/yy&isinCode='+isin+'&selectedMep=1&indexCompo=&quote=on&time=on&volume=on&typeDownload=1'
  page = urllib.urlopen(url)
  texte = page.read()
  return texte

def lire_isin_2616(isin):
  url = 'http://www.euronext.com/tools/datacentre/dataCentreDownloadExcell.jcsv?lan=FR&cha=2616&fileFormat=txt&separator=,&dateFormat=dd/MM/yy&isinCode='+isin+'&selectedMep=1&indexCompo=&quote=on&time=on&volume=on&typeDownload=1'
  page = urllib.urlopen(url)
  texte = page.read()
  return texte

def lire_infos_isin(isin):
  # print 'isin =',isin
  url = 'http://www.euronext.com/tools/datacentre/dataCentreDownloadExcell.jcsv?lan=FR&cha=2593&fileFormat=txt&separator=.&dateFormat=dd/MM/yy&isinCode='+isin+'&selectedMep=1&typeDownload=4'
  page = urllib.urlopen(url)
  texte = page.read()
  return texte

def format_infos(s):
  if s == '':
    return []
  t = s.split('\n')[3].split(';')
  return t

def format_infos_isin(isin):
  # print 'isin=', isin
  return format_infos(lire_infos_isin(isin))

def lire_euronext(v):
  # return lire_isin(isin(cours,v))
  return lire_isin(isin_nom(v))

pf1=[['ALTEN',29],['BOURBON',17],['CHRISTIAN DIOR',9],['EURAZEO',10],['FAURECIA',32],['GDF SUEZ',3],['HERMES',1],['LVMH',7],['NATIXIS',120],['NEXITY',3],['RHODIA',40],['SECHILIENNE',3],['SUEZ ENV',3],['TRIGANO',35],['VINCI',3],['FONC',6],['SAINT',12]]

pf=[['ALTEN',29],['BOURBON',17],['CHRISTIAN DIOR',3],['EURAZEO',10],['FAURECIA',6],['GDF SUEZ',3],['HERMES',1],['LVMH',7],['NATIXIS',30],['NEXITY',3],['RHODIA',0],['SECHILIENNE',3],['SUEZ ENV',3],['TRIGANO',8],['VINCI',3],['FONC',6],['SAINT',3],['VILMORIN',6]]

def valor1(a):
 s=lire_euronext(a)
 t=s.split('\r\n')
 l=len(t)
 x=t[6]
 u=x.split(';')
 v=float1(u[2])
 return v
 
def valor(pf,at):
 v=0
 for x in pf:
  v1=valor1(x[0])
  v2=v1*x[1]
  v=v+v2
  if at:
    #c=coursval(cours,x[0])
    c=cours_nom_jours(x[0],-28,0)
    q_mme = q_repete1 (init_mme, etape_mme, c, 28)
    q_cci = q_repete1 (init_cci, etape_cci, c, 14)
    q_indics=q_repete1gsc(init_indics,etape_indics,graphe_indics,c,po)
  # print(str(x[1])+'\t'+str(v1)+'\t'+str(v2)+'\t'+str(q_mme[0])+'\t'+str(q_cci[6])+'\t'+str(q_cci[0])+'\t'+x[0])
  #print "%15s %3d %6.2f %7.2f %6.2f %6.2f %d" % (x[0], x[1], v1, v2, q_mme[0], q_cci[6], q_cci[0])
    #print "%3d %6.2f %7.2f\t%6.2f %6.2f %d %s" % (x[1], v1, v2, q_mme[0], q_cci[6], q_cci[0], x[0])
    print "%3d %6.2f %7.2f\t%6.2f %6.2f %d %6.2f %s" % (x[1], v1, v2,q_mme[0], q_cci[6], q_cci[0], q_indics.s, x[0])
  else:
    print(str(x[1])+'\t'+str(v1)+'\t'+str(v2)+'\t'+x[0])
 return v

def at():
  for cv in cours:
    a = cv[0][1]
    q_mme = q_repete1 (init_mme, etape_mme, cv, 28)
    q_cci = q_repete1 (init_cci, etape_cci, cv, 14)
    print "%6.2f %6.2f %d\t%s" % (q_mme[0], q_cci[6], q_cci[0], a)

def secondes(h):
 t=h.split(':')
 s=int(t[0])*3600+int(t[1])*60+int(t[2])
 return s

def btn():
 return 0

# wd=200
# hg=200

t0lc=secondes('09:00:00')
t1lc=secondes('17:35:00')-t0lc

def graphid(a):
 s=lire_euronext(a)
 c=s.split('\r\n')
 m=Tk()
 e=Entry(m)
 #m.focus_set()
 #m.settopwindow()
 w=Canvas(m,width=wd,height=hg)
 w.pack(side=LEFT)
 b=Button(m,text=' ',command=btn)
 b.pack()
 #w.create_line(1,1,199,199,fill='blue')
 xxx=((c[6].split(';'))[2])
 #print ord(xxx[1])
 clo=float1((c[6].split(';'))[2])
 # clo=float(((c[6].split(';'))[2]).replace(' ','').replace(',','.').replace(' ','').replace('\t','').replace('\xA0',''))
 x=wd-1
 y=hg/2
 for i in range(6,len(c)-1):
  u=c[i].split(';')
  t=secondes(u[0])
  xp=x
  yp=y
  x=(float(t-t0lc)/float(t1lc))*wd
  #ct=float(((c[i].split(';'))[2]).replace(',','.').replace(' ' ,''))
  ct=float1((c[i].split(';'))[2])
  y=hg/2-((ct/clo)-1.0)*hg*10
  #print('t='+str(t)+' x='+str(x)+' y='+str(y))
  w.create_line(xp,yp,x,y,fill='blue')
 e.focus_set()
 mainloop()

