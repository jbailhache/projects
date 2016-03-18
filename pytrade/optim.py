
def optim(f,p,x,n):
 v=f(p,x)
 l=len(x)
 m=2
 for i in range(n):
  mi=m**(1/float(i+1))
  for j in range(l):
   a=x[j]
   print 'i=',i,' mi=',mi,' j=',j,' v=',v,' a=',a
   if i%2==0:
    x[j]=a/mi
   else:
    x[j]=a*mi
   w=f(p,x)
   print '(1) w=', w,' x[j]=',x[j]
   if w>v:
    v=w
   else:
    if i%2==0:
     x[j]=a*mi
    else:
     x[j]=a/mi
    w=f(p,x)
    print '(2) w=',w,' x[j]=',x[j]
    if w>v:
     v=w
    else:
     x[j]=a
 return v

  