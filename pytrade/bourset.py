
dircoursvista = 'c:\\users\\jacques\\bourse\\cours\\'
dircoursppc = '\\MicroDrive\\carte\\bourse\\cours\\'
dircoursxp = 'c:\\jacques\\bourse\\cours\\'

# lmois = ['0511', '0512']
# lmois = lmois + ['0601', '0602', '0603', '0604', '0605', '0606',
lmois0a = ['0301', '0302', '0303', '0304', '0305', '0306', '0307', '0308', '0309', '0310', '0311', '0312', '0401', '0402', '0403', '0404', '0405', '0406', '0407', '0408', '0409', '0410', '0411', '0412', '0501', '0502', '0503', '0504', '0505', '0506', '0507', '0508', '0509', '0510', '0511', '0512'] 
lmois0 = ['0601', '0602', '0603', '0604', '0605', '0606']
lmois1 = ['0607', '0608', '0609', '0610', '0611', '0612']
lmois1 = lmois1 + ['0701', '0702', '0703', '0704', '0705', '0706', '0707', '0708', '0709', '0710'] 
lmois2 = ['0711', '0712'] 
lmois2 = lmois2 + ['0801', '0802', '0803', '0804', '0805', '0806', '0807', '0808', '0809', '0810']
lmois3 = ['0811','0812','0901','0902','0903']
lmois = lmois1 + lmois2 + lmois3

lnfvista = [(dircoursvista + 'srd-' + mois + '.xls') for mois in lmois]
lnfppc = [(dircoursppc + 'srd-' + mois + '.xls') for mois in lmois2]
lnfxp = [(dircoursxp + 'srd-' + mois + '.xls') for mois in lmois]

cac40 = []
cac40 = cac40 + ['AIR FRANCE - KLM']
cac40 = cac40 + ['CREDIT AGRICOLE']
cac40 = cac40 + ['EADS']
cac40 = cac40 + ['AIR LIQUIDE']
cac40 = cac40 + ['CARREFOUR']
cac40 = cac40 + ['TOTAL']
cac40 = cac40 + ['L\'OREAL']
cac40 = cac40 + ['VALLOUREC']
cac40 = cac40 + ['ACCOR']
cac40 = cac40 + ['BOUYGUES']
cac40 = cac40 + ['LAFARGE']
cac40 = cac40 + ['SANOFI-AVENTIS']
cac40 = cac40 + ['AXA']
cac40 = cac40 + ['GROUPE DANONE']
cac40 = cac40 + ['PERNOD-RICARD']
cac40 = cac40 + ['LVMH MOET HENNESSY']
cac40 = cac40 + ['MICHELIN']
cac40 = cac40 + ['PPR']
cac40 = cac40 + ['PEUGEOT SA']
cac40 = cac40 + ['ESSILOR INTL']
cac40 = cac40 + ['SCHNEIDER ELECTRIC']
cac40 = cac40 + ['VEOLIA ENVIRON']
cac40 = cac40 + ['UNIBAIL-RODAMCO']
cac40 = cac40 + ['SAINT-GOBAIN']
cac40 = cac40 + ['CAP GEMINI']
cac40 = cac40 + ['VINCI']
cac40 = cac40 + ['VIVENDI']
cac40 = cac40 + ['DEXIA']
cac40 = cac40 + ['STMICROELECTRONICS']
cac40 = cac40 + ['ALCATEL LUCENT']
cac40 = cac40 + ['LAGARDERE SCA']
cac40 = cac40 + ['SOCIETE GENERALE A']
cac40 = cac40 + ['BNP PARIBAS']
cac40 = cac40 + ['RENAULT']
cac40 = cac40 + ['FRANCE TELECOM']
cac40 = cac40 + ['GDF SUEZ']
cac40 = cac40 + ['ALSTOM']
cac40 = cac40 + ['EDF']
# cac40 = cac40 + ['ARCELORMITTAL']

select = []
select = select + ['HERMES']
select = select + ['ALTEN']
select = select + ['ILIAD']
select = select + ['BIOMERIEUX']
select = select + ['AIR FRANCE - KLM']
select = select + ['CREDIT AGRICOLE']
select = select + ['EADS']
# select = select + ['AIR LIQUIDE']
select = select + ['CARREFOUR']
# select = select + ['TOTAL']
select = select + ['L\'OREAL']
# select = select + ['VALLOUREC']
select = select + ['ACCOR']
select = select + ['BOUYGUES']
select = select + ['LAFARGE']
select = select + ['SANOFI-AVENTIS']
select = select + ['AXA']
# select = select + ['GROUPE DANONE']
# select = select + ['PERNOD-RICARD']
select = select + ['LVMH MOET HENNESSY']
select = select + ['MICHELIN']
select = select + ['PPR']
select = select + ['PEUGEOT SA']
# select = select + ['ESSILOR INTL']
select = select + ['SCHNEIDER ELECTRIC']
select = select + ['VEOLIA ENVIRON']
select = select + ['UNIBAIL-RODAMCO']
select = select + ['SAINT-GOBAIN']
select = select + ['CAP GEMINI']
# select = select + ['VINCI']
select = select + ['VIVENDI']
select = select + ['DEXIA']
select = select + ['STMICROELECTRONICS']
select = select + ['ALCATEL LUCENT']
select = select + ['LAGARDERE SCA']
select = select + ['SOCIETE GENERALE A']
select = select + ['BNP PARIBAS']
select = select + ['RENAULT']
select = select + ['FRANCE TELECOM']
select = select + ['GDF SUEZ']
# select = select + ['ALSTOM']
# select = select + ['EDF']
# select = select + ['ARCELORMITTAL']

select2 = select

def lirecours(nom):
  f = open (nom,"r")
  hdr = f.readline()
  print hdr
  c=[]
  code=""
  d = []
  for line1 in f:
    line=line1[0:len(line1)-1]
    r=line.split('\t')
    if (len(r)>7):
      for i in range(3,8):
        r[i]=float(r[i].replace(',','.'))
    if (r[0]!=code):
      if code != "":
        c = c + [d]
      code=r[0]
      d = []
    d = d + [r]
  return c

def lirecours1(nom):
  f = open (nom,"r")
  c=[]
  code=""
  d = []
  for line1 in f:
    line=line1[0:len(line1)-1]
    r=line.split('\t')
    if (len(r)>7):
      for i in range(3,8):
        r[i]=float(r[i].replace(',','.'))
    if (r[0]!=code):
      if code != "":
        c = c + [d]
      code=r[0]
      d = []
    d = d + [r]
  c=c+[d]
  return c

def lirecourslf(lnf):
  c=[]
  for nf in lnf:
    print nf
    f=open(nf,"r")
    hdr=f.readline()
    for line1 in f:
      line=line1[0:len(line1)-1]
      r=line.split('\t')
      if len(r)>7:
        for i in range(3,8):
          r[i]=float(r[i].replace(',','.'))
      trouve=0
      for i in range(len(c)):
        if c[i][0][0]==r[0]:
         if len(r)>=8:
          c[i]=c[i]+[r]
          trouve=1
      if trouve==0:
        # if len(c[len(c)-1])<=1:
        #  c=c[0:len(c)-1]
        c=c+[[r]]
  cr = []
  for a in c:
    if len(a)>1:
      cr = cr + [a]
  return cr

def cloval(c,v):
  for cv in c:
    if cv[0][1].find(v)==0:
      return [r[6] for r in cv]
  return []

def coursval(cours,v):
  for cv in cours:
   if len(cv[0])>1:
    if cv[0][1].find(v) == 0:
      return cv
  return []

def courslval(cours,lv):
  c = []
  for v in lv:
    c = c + [coursval(cours,v)]
  return c

def ecrirecours(c,nf):
  f = open (nf,"w")
  for x in c:
    for i in range(7):
      f.write(str(x[i]).replace('.',','))
      f.write('\t')
    f.write(str(x[7]))
    f.write('\n')
  f.close()

def noms(c):
  return [x[0][1] for x in c]

def cloture(c):
  return [[y[6] for y in x] for x in c]

def norm1(y):
  return [z/y[0] for z in y]

def norm(x):
  return [norm1(y) for y in x]

def graphval(c):
  n = noms(c)
  cl = cloture(c)
  cln = norm(cl)
  x = [[l[i] for i in range(1,len(l)-1)] for l in cln]
  y = centrer(x)
  sluc = acpb(y)
  graph (sluc[2], n, 300, 200, -1, 1, -0.5, 0.5)
  return sluc

def afcours(c,t):
  cl = [[y[6]] for y in c]
  courbes(cl,['blue'],wd2,hg,t)







