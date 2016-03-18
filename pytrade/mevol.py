
def repevolc(pop,param,c):
  f = open('repevolc.txt','a')
  # pop = popinit(heur,param)
  pop = pop[0:param[1]]
  print "l0=%7.1f seed(%d) maxi=%d testegal=%d pmoy=%.2f pmut=%.2f : " % (param[7], param[0], param[1], param[4], param[5], param[6]),
  # f.write ("l0=%7.1f seed(%d) maxi=%d te=%d pmoy=%.2f pmut=%.2f : " % (param[7], param[0], param[1], param[4], param[5], param[6]))
  f.write ("%d %d %d %.2f %.2f : " % (param[0], param[1], param[4], param[5], param[6]))
  # l0 = param[7]
  seed(param[0])
  t = 0
  while t<=param[2]:
    print 't=', t, ' v=', pop[0][0]
    pop = evolc(pop,param,c)
    if t % param[3] == 0:
      print "*** %6.1f ***" % pop[0][0]
      f.write("%6.1f " % pop[0][0])
    t = t + 1
  print ''
  f.write('\n')
  f.close()

def mvaleur(param):
  p0=popinit(heur,300)
  p1=repevolc(p0,param,cours)
  return p1[0][0]

def mvaleursxs(l):
  return [[mvaleur(param),param] for param in l]

def mpopinit1():
  pop=[]
  sd = 26
  tm = 100
  l = 1000.0
  for maxi in [24,48,96]:
    for testegal in [0,1]:
      for pmoy in [0.1, 0.5, 0.9]:
        for pmut in [0.1, 0.5, 0.9]:
          pop = pop + [[sd, maxi, tm, tm, testegal, pmoy, pmut, l]]
  return pop

#def mpopinit():
 # p1=mpopinit1()
  #p=[[mvaleur(param),param] for param in p1]
  #return p

def mpopinit(n):
  l = mpopinit1()
  p = mvaleursxs(l)
  r = p
  while len(r)<n:
    r=r+p
  r=r[0:n]
  return r

def mrandomx(x):
  y=x
  y[1]=randint(4,127)
  y[4]=randint(0,1)
  y[5]=uniform(0.0,1.0)
  y[6]=uniform(0.0,1.0)
  return y

def mcomb(x,y,param):
  if (param[4]!=0) and (x==y):
    return mrandomx(x)
  z=x
  b=randint(0,1)
  if b==1: z[4]=y[4]
  b=uniform(0.0,1.0)
  if b>param[5]:
    for i in [1,5,6]:
      b = randint(0,1)
      if b==1: z[i]=y[i]
  else:
    z[1]=(x[1]+y[1])/2
    for i in [5,6]: z[i]=(x[i]+y[i])/2.0
  b=uniform(0.0,1.0)
  if b<param[6]:
    i=randint(0,3)
    if i==0:
      z[1]=randint(4,127)
    elif i==1:
      z[4]=randint(0,1)
    elif i==2:
      z[5]=uniform(0.0,1.0)
    else:
      z[6]=uniform(0.0,1.0)
  return z

def mevolc (pop,param,c):
  pop = tripop(pop)
  pop = pop[0:param[1]]
  i = randint(0,param[1]-1)
  j = randint(0,param[1]-1)
  x = pop[i][1]
  y = pop[j][1]
  z = mcomb(x,y,param)
  v = mvaleurc(z,c)
  print 'valeur = ',v
  pop = inser([v,z],pop)
  pop = pop[0:param[1]]
  f = open('pop.txt', 'w')
  f.write(str(pop))
  f.close()
  return pop

 
def mrepevolc(pop,param,c):
  f = open('mrepevolc.txt','a')
  # pop = popinit(heur,param)
  pop = pop[0:param[1]]
  print "l0=%7.1f seed(%d) maxi=%d testegal=%d pmoy=%.2f pmut=%.2f : " % (param[7], param[0], param[1], param[4], param[5], param[6]),
  # f.write ("l0=%7.1f seed(%d) maxi=%d te=%d pmoy=%.2f pmut=%.2f : " % (param[7], param[0], param[1], param[4], param[5], param[6]))
  f.write ("%d %d %d %.2f %.2f : " % (param[0], param[1], param[4], param[5], param[6]))
  # l0 = param[7]
  seed(param[0])
  t = 0
  while t<=param[2]:
    print 't=', t, ' v=', pop[0][0]
    pop = mevolc(pop,param,c)
    if t % param[3] == 0:
      print "*** %6.1f ***" % pop[0][0]
      f.write("%6.1f " % pop[0][0])
    t = t + 1
  print ''
  f.write('\n')
  f.close()


def mtestparamc(pop):
  # f = open ('testparamc.txt', 'w')
  # for l in [500, 1000, 2000]:
  l = 1000.0
  for maxi in [24, 48, 96]:
      for testegal in [0, 1]:
        for pmoy in [0.1, 0.5, 0.9]:
          for pmut in [0.1, 0.5, 0.9]:
           for s in [26, 31]:
            for c in [c2,c1]:
             param = [s, maxi, 500, 100, testegal, pmoy, pmut, l]
             mrepevolc(pop,param,c)
  # f.close()

mexparam=[26,32,100,20,1,0.1,0.5,1000.0]
