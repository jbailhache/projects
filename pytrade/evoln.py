
def mut(x):
  y=x
  i=randint(0,len(x)-1)
  y[i]=uniform(-1.0,1.0) 
  return y

def vari(x,t,param):
  y=x
  for i in range(len(y)):
    y[i]=y[i]+gauss(0.0,sigmat(t,param))
    if y[i]<-1.0: y[i]=-1.0
    if y[i]>1.0: y[i]=1.0
  return y

def hybrid(x,y):
  z=x
  for i in range(len(z)):
    b=randint(0,1)
    if b==1: z[i]=y[i]
  return z

def moy(x,y):
  return [(x[i]+y[i])/2.0 for i in range(x)]

def evoln(pop,param,c,t):
  pop=tripop(pop)
  pop=pop[0:param[1]]
  x=randx()
  v=valeurc(x,c)
  npop=inser([v,x],pop)
  for vx in pop:
    x=mut(vx[1])
    v=valeurc(x,c)
    npop=inser([v,x],npop)
    x=vari(vx[1],t,param)
    v=valeurc(x,c)
    npop=inser([v,x],npop)
    i=randint(0,param[1]-1)
    x=hybrid(vx[1],pop[i][1])
    v=valeurc(x,c)
    npop=inser([v,x],npop)

  pop = npop[0:param[1]]
  f = open('pop.py', 'w')
  writex(f,pop[0])
  f.write('\n')
  f.write('pop = ' + str(pop)+'\n')
  f.close()
  # fpops = open('pops.txt','a')
  # writex(fpops,pop[0])
  # fpops.write('\n')
  # fpops.write(str(pop))
  # fpops.close()
  fb = open('evoln.txt','a')
  fb.write(" t=%d : %8.3f %8.3lf " % (t,pop[0][0],v))
  fb.write(str(pop[0][1]))
  fb.write(' ')
  # fb.write(str(z))
  fb.write('\n')
  fb.close()

  return pop


def repevoln(pop,param,c):
  f = open('repevoln.txt','a')
  # pop = popinit(heur,param)
  pop = pop[0:param[1]]
  print "l0=%7.1f seed(%d) maxi=%d testegal=%d pmoy=%.2f pmut=%.2f : " % (param[7], param[0], param[1], param[4], param[5], param[6]),
  # f.write ("l0=%7.1f seed(%d) maxi=%d te=%d pmoy=%.2f pmut=%.2f : " % (param[7], param[0], param[1], param[4], param[5], param[6]))
  f.write ("%d %d %d %.2f %.2f %.2f %.2f : " % (param[0], param[1], param[4], param[5], param[8], param[9], param[10]))
  # l0 = param[7]
  if param[0] != 0:
    seed(param[0])
  t = 0
  while t<=param[2]:
    print 't=', t, ' v=', pop[0][0]
    pop = evoln(pop,param,c,t)
    if t % param[3] == 0:
      print "*** %6.1f ***" % pop[0][0]
      f.write("%6.1f " % pop[0][0])
      # fb = open('repevolcvb.txt','a')
      # fb.write(" t=%d : %8.3f " % (t,pop[0][0]))
      # fb.write(pop[0][1])
      # fb.close()
    t = t + 1
  print ''
  f.write('\n')
  f.close()
  return pop

   