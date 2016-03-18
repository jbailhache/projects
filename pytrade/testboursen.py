
cours = lirecourslf(lnfn)

lc1=[0 for i in range(8)]

lc1[0] = coursval(cours,'ALTEN')[120:330]
lc1[1] = coursval(cours,'EADS')[0:300]
lc1[2] = coursval(cours,'AXA')[70:320]
lc1[3] = coursval(cours,'LVMH')[0:300]
lc1[4] = coursval(cours,'PPR')[40:350]
lc1[5] = coursval(cours,'VIVENDI')[60:330]
lc1[6] = coursval(cours,'ILIAD')[140:360]
lc1[7] = coursval(cours,'CREDIT AGRICOLE')[0:210]

lc2 = [0 for i in range(3)]
lc2[0] = coursval(cours,'AXA')[0:100]
lc2[1] = coursval(cours,'AXA')[100:200]
lc2[2] = coursval(cours,'AXA')[200:300]

lc3 = [0 for i in range(3)]
lc3[0] = coursval(cours,'AXA')[0:100]
lc3[1] = coursval(cours,'PPR')[0:100]
lc3[2] = coursval(cours,'ALTEN')[0:100]

lc4 = [0 for i in range(3)]
lc4[0] = coursval(cours,'AXA')[0:100]
lc4[1] = coursval(cours,'PPR')[100:200]
lc4[2] = coursval(cours,'ALTEN')[200:300]

