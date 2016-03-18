
import math

def heurmacd(sel):
  bestk = 0
  bestl = []
  bestp = []
  for i1 in range(10):
    l1 = i1/1.0
    p1 = math.exp(l1)
    for i2 in range(10):
      l2 = i2/1.0
      p2 = math.exp(l2)
      for i3 in range(10):
        l3 = i3/1.0
        p3 = math.exp(l3)
        r = moyind (sel, macd, [p1, p2, p3])
        print p1, p2, p3, r[0]
        if r[1] > bestk:
          bestk = r[1]
          bestl = [l1, l2, l3]
          bestp = [p1, p2, p3]
  return [bestk, bestl, bestp]
