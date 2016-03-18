
execfile('ad.py')
execfile('ip.py')
print 'courslval'
cs3=courslval(cours,sel3)
print 'matrind'
mi3p=matrind(cs3,p)
print 'centred'
mi3pcr=centred(mi3p)
print 'acp'
sluc3pcr=acp(mi3pcr)
[s,l,u,c]=sluc3pcr
p.u=u
npix=5
wd=200
hg=200
print 'tabs_ip'
tabs=tabs_ip(cs3,p)
print 'graph_tabs'
graph_tabs(tabs,0,1,1)
print 'tabsn'
tn=tabsn(tabs)
print 'graph_tabsn'
graph_tabsn(tn,0,1,1)

