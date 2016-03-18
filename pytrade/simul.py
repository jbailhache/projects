
execfile('load1.py')

c=lirecourslf(['cours/srd-0901.xls'])

lf = [
'cours/srd-0801.xls',
'cours/srd-0802.xls',
'cours/srd-0803.xls',
'cours/srd-0804.xls',
'cours/srd-0805.xls',
'cours/srd-0806.xls',
'cours/srd-0807.xls',
'cours/srd-0808.xls',
'cours/srd-0809.xls',
'cours/srd-0810.xls',
'cours/srd-0811.xls',
'cours/srd-0812.xls',
'cours/srd-0901.xls',
'cours/srd-0902.xls',
'cours/srd-0903.xls',
'cours/srd-0904.xls',
'cours/srd-0905.xls',
'cours/srd-0906.xls',
'cours/srd-0907.xls',
'cours/srd-0908.xls',
'cours/srd-0909.xls',
'cours/srd-0910.xls',
'cours/srd-0911.xls',
'cours/srd-0912.xls']

def libs(c):
 l=[]
 for c1 in c:
  l=l+[c1[0][1]]
 return l

def dates1(c):
 d=[]
 for c1 in c[0]:
  d=d+[c1[2]]
 return d

def order(d1,d2):
 a1 = d1.split('/')
 a2 = d2.split('/')
 an1 = int(a1[2])
 if an1<2000:
  an1=2000+an1
 an2 = int(a2[2])
 if an2<2000:
  an2=2000+an2
 n1 = int(a1[0])+100*int(a1[1])+10000*an1
 n2 = int(a2[0])+100*int(a2[1])+10000*an2
 # print "n1=", n1, " n2=", n2
 if (n2 < n1):
  return -1
 if (n2 > n1):
  return 1
 return 0
  
def dates(c):
 d=[]
 for c1 in c:
  for c2 in c1:
   found=0
   for d1 in d:
    if d1==c2[2]:
     found=1
     break
   if found==0:
    # print "nouvelle date: ", c2[2], "d=", d
    d=d+['99/99/99']
    for i in range(len(d)):
     if order(c2[2],d[i])>=0:
      # print c2[2], " est avant ", d[i] 
      for j in range(len(d)-1,i,-1):
       # print "d[j-1]=",d[j-1]
       # print "j=",j
       d[j]=d[j-1]
      d[i]=c2[2]
      break
    d[len(d)-1]=c2[2]
 return d

def cld(c,l,d):
 for cl in c:
  if cl[0][1][0:len(l)]==l:
   for r in cl:
    if r[2]==d:
     return r

def civd(c,iv,id,d):
 for i in range(id):
  for r in c[iv]:
   # print "r=",r
   if r[2]==d[id-i]:
    return r
  # if id<=0:
  #  return []
  # print "cours non trouv�"
  # return civd(c,iv,id-1,d)
 return []

def var(c,iv,id,d,ic):
 # return (c[iv][id][ic]-c[iv][id-1][ic]) / c[iv][id-1][ic]
 c1a = civd(c,iv,id-1,d)
 # print "c1a=",c1a
 if len(c1a)<8:
  return 0
 c1 = c1a[ic]
 # c1 = civd(c,iv,d1)[ic]
 c2a = civd(c,iv,id,d)
 if len(c2a)<8:
  return 0
 c2 = c2a[ic]
 return (c2 - c1) / c1 

def simul(cours,ic,fr,cap,seuil,p):
 l=libs(cours)
 d=dates(cours) 
 nv=len(l)
 nd=len(d)
 # varini=[var(cours,iv,1,ic) for iv in range(nv)] 
 varini = [var(cours,iv,1,d,ic) for iv in range(nv)]
 ipfb=0
 pfb=varini[0]
 for i in range(nv):
  if varini[i]<pfb:
   pfb=varini[i]
   ipfb=i
 # cva=cours[ipfb][1][ic]
 cva = civd(cours,ipfb,1,d)[ic]
 na=int((cap-fr)/cva)
 if na<0:
  na=0
 if na>0:
  liq=cap-na*cva-fr
 else:
  liq=cap
 iva=ipfb
 if p:
  print
  print d[1],": achat initial ",na," ",l[iva]," au cours de ",cva," valorisation ",na*cva," liquidit�s ",liq
 for id in range(2,nd-1):
  nap=na
  ivap=iva
  cvap=cva
  varva=var(cours,iva,id,d,ic)
  vars=[var(cours,iv,id,d,ic) for iv in range(nv)]
  ipfb=0
  pfb=vars[0]
  for i in range(nv):
   if vars[i]<pfb:
    pfb=vars[i]
    ipfb=i
  if (varva - pfb >= seuil):
   # liq=liq+na*cours[iva][id][ic]-fr
   cvv = civd(cours,iva,id,d)[ic]
   if na>0:
    liq = liq + na * cvv - fr
   iva=ipfb
   # cva=cours[iva][id][ic]
   cva = civd(cours,iva,id,d)[ic]
   na=int((liq-fr)/cva)
   if na<0:
    na=0
   if na>0:
    liq=liq-na*cva-fr
   total = liq + na * cva
   if p:
    print 
    print d[id],": vente de ","%5d"%nap," ",l[ivap]," au cours de ","%6.2f"%cvv," valorisation ","%7.2f"%(nap*cvv)
    print d[id],": achat de ","%5d"%na ," ",l[iva] ," au cours de ","%6.2f"%cva ," valorisation ","%7.2f"%(na*cva)
    print d[id],": liquidit�s ","%7.2f"%liq," total ","%7.2f"%total
 if na>0:
  liq=liq+na*cva-fr
 if p:
  print
  print "capital final: ","%7.2f"%liq
  print
 return liq

def test_simul1(fr,cap,seuil):
 r = [simul(lirecourslf([lf[i]]),3,fr,cap,seuil,0) for i in range(len(lf))]
 print
 for x in r:
  print x
 print
 s = 0
 for x in r:
  s = s + x
 m = s / len(r)
 print "moyenne: ", m 
 print
 return m

def test_simul2(tc,fr,cap,seuil):
 r = [simul(tc[i],3,fr,cap,seuil,0) for i in range(len(lf))]
 print
 for x in r:
  print x
 print
 s = 0
 for x in r:
  s = s + x
 m = s / len(r)
 print "moyenne: ", m
 print
 return m

def test_simul3(fr,cap):
 tc = [lirecourslf([lf[i]]) for i in range(len(lf))]
 r = [[0.01*s,test_simul2(tc,fr,cap,0.01*s)] for s in range(1,21)]
 for x in r:
  print "%4.2f"%x[0]," : ","%7.2f"%x[1]
 print

def test_simul4(tc,fr,cap,seuil,a,b):
 r = [simul(tc[i],3,fr,cap,seuil,0) for i in range(b-a)]
 print
 for x in r:
  print x
 print
 s = 0
 for x in r:
  s = s + x
 m = s / len(r)
 print "moyenne: ", m
 print
 return m

def test_simul5(fr,cap,a,b,sm):
 tc = [lirecourslf([lf[i]]) for i in range(a,b)]
 r = [[0.01*s,test_simul4(tc,fr,cap,0.01*s,a,b)] for s in range(1,sm)]
 for x in r:
  print "%4.2f"%x[0]," : ","%7.2f"%x[1]
 print

