
from Tkinter import *

def test1():
  master=Tk()
  w=Canvas(master,width=200,height=160)
  w.pack(side=LEFT)
  b = Button (master, text=" ", command=btn)
  b.pack()
  w.create_rectangle(10,10,100,60,fill='#b0c070')
  for i in range(30):
    w.create_line(120+2*i,10,121+2*i,10,fill='#301090')
  mainloop() 

def btn():
  return 0

def graph(c,noms,wd,hg,minx,maxx,miny,maxy):
  master=Tk()
  w=Canvas(master,width=wd,height=hg)
  w.pack(side=LEFT)
  b = Button (master, text=" ", command=btn)
  b.pack()
  m=10
  x=m+(wd-2*m)*(-minx)/float(maxx-minx)
  y=m+(hg-2*m)*(1-(-miny)/float(maxy-miny))
  w.create_line(1,y,wd-1,y,fill='blue')
  w.create_line(x,1,x,hg-1,fill='blue')
  # w.create_circle
  for i in range(len(c)):
    ci = c[i]
    nom = noms[i]
    x = m + (wd-2*m) * (ci[0] - minx) / float (maxx - minx)
    y = m + (hg-2*m) * (1 - (ci[1] - miny) / float (maxy - miny))
    w.create_text (x, y, text=nom)
    print x, y, nom
  mainloop()

def graphxy(c,wd,hg):
  minx=0
  maxx=0
  miny=0
  maxy=0
  for xy in c:
    if xy[0]<minx: minx=xy[0]
    if xy[0]>maxx: maxx=xy[0]
    if xy[1]<miny: miny=xy[1]
    if xy[1]>maxy: maxy=xy[1]
  noms=range(len(c))
  graph(c,noms,wd,hg,minx,maxx,miny,maxy)

def graphtxy(c,wd,hg):
  minx=0
  maxx=0
  miny=0
  maxy=0
  for txy in c:
    if txy[1]<minx: minx=txy[1]
    if txy[1]>maxx: maxx=txy[1]
    if txy[2]<miny: miny=txy[2]
    if txy[2]>maxy: maxy=txy[2]
  master=Tk()
  w=Canvas(master,width=wd,height=hg)
  w.pack(side=LEFT)
  b = Button (master, text=" ", command=btn)
  b.pack()
  m=40
  x=m+(wd-2*m)*(-minx)/float(maxx-minx)
  y=m+(hg-2*m)*(1-(-miny)/float(maxy-miny))
  w.create_line(1,y,wd-1,y,fill='blue')
  w.create_line(x,1,x,hg-1,fill='blue')
  for txy in c:
    x = m + (wd-2*m) * (txy[1] - minx) / float (maxx - minx)
    y = m + (hg-2*m) * (1 - (txy[2] - miny) / float (maxy - miny)) 
    w.create_text(x,y,text=txy[0])
  mainloop()

def graphxyz(c,wd,hg):
  minx=0
  maxx=0
  miny=0
  maxy=0
  minz=0
  maxz=0
  for xyz in c:
    if xyz[0]<minx: minx=xyz[0]
    if xyz[0]>maxx: maxx=xyz[0]
    if xyz[1]<miny: miny=xyz[1]
    if xyz[1]>maxy: maxy=xyz[1]
    if xyz[2]<minz: minz=xyz[2]
    if xyz[2]>maxz: maxz=xyz[2]
  print str(minx) + ' ' + str(maxx) + ' ' + str(miny) + ' ' + str(maxy) + ' ' + str(minz) + ' ' + str(maxz)
  if -minz>maxz: mz=-minz
  else: mz=maxz
  if mz==0:
    mz=1
  master=Tk()
  w=Canvas(master,width=wd,height=hg,bg='white')
  w.pack(side=LEFT)
  b = Button (master, text=" ", command=btn)
  b.pack()
  m=10
  x=m+(wd-2*m)*(-minx)/float(maxx-minx)
  y=m+(hg-2*m)*(1-(-miny)/float(maxy-miny))
  w.create_line(1,y,wd-1,y,fill='blue')
  w.create_line(x,1,x,hg-1,fill='blue')
  r = 0.1
  xr1 = m+(wd-2*m)*(-r-minx)/float(maxx-minx)
  yr1 = m+(hg-2*m)*(1-(-r-miny))/float(maxy-miny)
  xr2 = m+(wd-2*m)*(r-minx)/float(maxx-minx)
  yr2 = m+(hg-2*m)*(1-(r-miny))/float(maxy-miny)
  w.create_rectangle(xr1,yr1,xr2,yr2,outline='grey')
  for ci in c:
    x = m + (wd-2*m) * (ci[0] - minx) / float (maxx - minx)
    y = m + (hg-2*m) * (1 - (ci[1] - miny) / float (maxy - miny)) 
    z = 128 + 126 * ci[2] / float(mz)
    col='#%02x%02x%02x' % (256-z, z, 0)
    # w.create_line(x,y,x+1,y,fill=col)
    w.create_line(x-1,y-1,x+2,y-1,fill=col)
    w.create_line(x-1,y,x+2,y,fill=col)
    w.create_line(x-1,y+1,x+2,y+1,fill=col)
    # w.create_rectangle(x,y,x+10,y+10,fill=col)
  for x in range(minx,maxx):
    cx = (x-m)/float(wd-2*m)*(maxx-minx)+minx
    y = m + (hg-2*m) * (1 - (cx - miny) / float (maxy - miny)) 
    z = 128 + 126 * cx / float(mz)
    if z<1: z=1
    if z>255: z=255
    col='#%02x%02x%02x' % (256-z, z, 0)
    w.create_line(x-1,y-1,x+2,y-1,fill=col)
    w.create_line(x-1,y,x+2,y,fill=col)
    w.create_line(x-1,y+1,x+2,y+1,fill=col)
  mainloop()

def graphxyp(c,wd,hg):
  minx=0
  maxx=0
  miny=0
  maxy=0
  minz=0
  maxz=0
  for xyz in c:
    if xyz[0]<minx: minx=xyz[0]
    if xyz[0]>maxx: maxx=xyz[0]
    if xyz[1]<miny: miny=xyz[1]
    if xyz[1]>maxy: maxy=xyz[1]
   
  print str(minx) + ' ' + str(maxx) + ' ' + str(miny) + ' ' + str(maxy) + ' '
  master=Tk()
  w=Canvas(master,width=wd,height=hg,bg='white')
  w.pack(side=LEFT)
  b = Button (master, text=" ", command=btn)
  b.pack()
  m=10
  x=m+(wd-2*m)*(-minx)/float(maxx-minx)
  y=m+(hg-2*m)*(1-(-miny)/float(maxy-miny))
  w.create_line(1,y,wd-1,y,fill='blue')
  w.create_line(x,1,x,hg-1,fill='blue')
  r = 0.1
  xr1 = m+(wd-2*m)*(-r-minx)/float(maxx-minx)
  yr1 = m+(hg-2*m)*(1-(-r-miny))/float(maxy-miny)
  xr2 = m+(wd-2*m)*(r-minx)/float(maxx-minx)
  yr2 = m+(hg-2*m)*(1-(r-miny))/float(maxy-miny)
  w.create_rectangle(xr1,yr1,xr2,yr2,outline='grey')
  for ci in c:
    x = m + (wd-2*m) * (ci[0] - minx) / float (maxx - minx)
    y = m + (hg-2*m) * (1 - (ci[1] - miny) / float (maxy - miny)) 
    col='#%02x%02x%02x' % (0, 0, 0)
    # w.create_line(x,y,x+1,y,fill=col)
    w.create_line(x-1,y-1,x+2,y-1,fill=col)
    w.create_line(x-1,y,x+2,y,fill=col)
    w.create_line(x-1,y+1,x+2,y+1,fill=col)
    # w.create_rectangle(x,y,x+10,y+10,fill=col)
  for x in range(minx,maxx):
    cx = (x-m)/float(wd-2*m)*(maxx-minx)+minx
    y = m + (hg-2*m) * (1 - (cx - miny) / float (maxy - miny)) 
    col='#%02x%02x%02x' % (0,0,0)
    w.create_line(x-1,y-1,x+2,y-1,fill=col)
    w.create_line(x-1,y,x+2,y,fill=col)
    w.create_line(x-1,y+1,x+2,y+1,fill=col)
  mainloop()

C = [[0,0],[1,0],[0,1],[1,1],[2,1]]
n = ['O','A','B','C','D']

# graph (C, n, 200, 150 , -1, 3, -1, 2)

def courbes(a,colors,wd,hg,t):
  master=Tk()
  w=Canvas(master,width=wd,height=hg)
  w.pack(side=LEFT)
  w.create_text(wd/2,hg-10,text=t)
  b = Button (master, text=" ", command=btn)
  b.pack()
  min=10000
  max=-10000
  for b in a:
    for v in b:
      if v<min:
        min=v
      if v>max:
        max=v
  nl=16
  for i in range(nl):
  #   w.create_line(wd*(i+0.5)/float(nl),1,wd*(i+0.5)/float(nl),hg-1,fill='grey')
    w.create_line(1,hg*(i+0.5)/float(nl),wd-1,hg*(i+0.5)/float(nl),fill='grey')
  for t in range(1,len(a)):    
    tp=t-1
    xp=tp*wd/len(a)
    x=t*wd/len(a)
    if t % 10 == 0:
      if t % 100 == 0:
        couleur = 'black'
      else:
        couleur = 'grey'
      w.create_line (x, 1, x, hg, fill=couleur)
    for i in range(len(a[t])):
      vp=a[tp][i]
      yp=hg-(vp-min)*hg/(max-min)
      v=a[t][i]
      y=hg-(v-min)*hg/(max-min)
      w.create_line(xp,yp,x,y,fill=colors[i])
  mainloop()

a1=[[10,12],[14,11],[11,9],[10,10],[12,11]]
colors=['blue','red']

  


