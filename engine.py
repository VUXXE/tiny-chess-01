import json,os,random,sys,urllib.error as I,urllib.request as T
VAL=[0,100,320,330,500,900,0]
MATE=100000
NODES=140000
START="rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0"
KN=[-33,-31,-18,-14,14,18,31,33]
KI=[-17,-16,-15,-1,1,15,16,17]
BD=[-17,-15,15,17]
RD=[-16,-1,1,16]
D=[(ord(c)-80)*5 for c in "PPPPPPPPZZZZZZZZRRTVVTRRQQRUURQQPPPTTPPPQONPPNOQQRRLLRRQPPPPPPPPFHJJJJHFHLPPPPLHJPRSSRPJJQSTTSQJJPSTTSPJJQRSSRQJHLPQQPLHFHJJJJHFLNNNNNNLNPPPPPPNNPQRRQPNNQQRRQQNNPRRRRPNNRRRRRRNNQPPPPQNLNNNNNNLPPPPPPPPQRRRRRRQOPPPPPPOOPPPPPPOOPPPPPPOOPPPPPPOOPPPPPPOPPPQQPPPLNNOONNLNPPPPPPNNPQQQQPNOPQQQQPOPPQQQQPONQQQQQPNNPQPPPPNLNNOONNLJHHFFHHJJHHFFHHJJHHFFHHJJHHFFHHJLJJHHJJLNLLLLLLNTTPPPPTTTVRPPRVTFHJLLJHFJLNPPNLJJNTVVTNJJNVXXVNJJNVXXVNJJNTVVTNJJJPPPPJJFJJJJJJF"]
PSV=[[0]*128 for _ in range(13)]
for p in range(1,7):
 for q in range(128):
  if q&136:continue
  r,f=q>>4,q&7
  v=VAL[p]+D[(p-1)*64+(7-r)*8+f]
  PSV[p+6][q]=v
  PSV[-p+6][q]=-(VAL[p]+D[(p-1)*64+r*8+f])
CK=[15]*128
CK[0]=13
CK[7]=14
CK[4]=12
CK[112]=7
CK[119]=11
CK[116]=3
_r=random.Random(20261117)
ZP=[[_r.getrandbits(64) for _ in range(128)] for _ in range(13)]
ZC=[_r.getrandbits(64) for _ in range(16)]
ZE=[_r.getrandbits(64) for _ in range(8)]
ZS=_r.getrandbits(64)
B=[0]*128
S=1
C=0
E=-1
H=0
Z=0
SC=0
KS=[4,116]
U=[]
PATH=[]
CNT=[0]*13
ND=0
LIM=0
ABT=False
TTK,TTD,TTF,TTS,TTM=[[0]*131072 for _ in range(5)]
KIL=[[0,0] for _ in range(128)]
HST=[0]*1664
def F(fen):
 global S,C,E,H,Z,SC
 for i in range(128):B[i]=0
 for i in range(13):CNT[i]=0
 U.clear()
 PATH.clear()
 Z=0
 SC=0
 p=fen.split()
 q=112
 for ch in p[0]:
  if ch=="/":q-=24
  elif ch.isdigit():q+=int(ch)
  else:
   pc="pnbrqk".index(ch.lower())+1
   sg=1 if ch.isupper() else -1
   B[q]=pc*sg
   if pc==6:KS[sg<0]=q
   Z^=ZP[B[q]+6][q]
   CNT[B[q]+6]+=1
   if pc!=6:SC+=PSV[B[q]+6][q]
   q+=1
 S=1 if p[1]=="w" else -1
 if S==-1:Z^=ZS
 C=0
 for ch in p[2]:
  if ch in "KQkq":C|=1<<"KQkq".index(ch)
 Z^=ZC[C]
 if p[3]=="-":E=-1
 else:
  E=(ord(p[3][1])-49)*16+ord(p[3][0])-97
  Z^=ZE[E&7]
 H=int(p[4])
 PATH.append(Z)
def A(sq,by):
 for t in (sq-15*by,sq-17*by):
  if not t&136 and B[t]==by:return True
 for d in KN:
  t=sq+d
  if not t&136 and B[t]==2*by:return True
 for d in KI:
  t=sq+d
  if not t&136 and B[t]==6*by:return True
 for d in RD:
  t=sq+d
  while not t&136:
   p=B[t]
   if p:
    if p==4*by or p==5*by:return True
    break
   t+=d
 for d in BD:
  t=sq+d
  while not t&136:
   p=B[t]
   if p:
    if p==3*by or p==5*by:return True
    break
   t+=d
 return False
def M(m):
 global S,C,E,H,Z,SC
 f=m&127
 t=m>>7&127
 pr=m>>14&7
 pc=B[f]
 cap=B[t]
 cs=t
 sd=16*S
 si=S<0
 if (pc==1 or pc==-1) and t==E and cap==0:
  cs=t-sd
  cap=B[cs]
 U.append((m,cap,cs,C,E,H,Z,SC))
 if pc!=6 and pc!=-6:SC+=PSV[pc+6][t]-PSV[pc+6][f]
 if cap:SC-=PSV[cap+6][cs]
 if pr:SC+=PSV[pr*S+6][t]-PSV[pc+6][t]
 if cs!=t:B[cs]=0
 Z^=ZP[pc+6][f]
 if cap:
  Z^=ZP[cap+6][cs]
  CNT[cap+6]-=1
 if pr:
  Z^=ZP[pr*S+6][t]
  CNT[pr*S+6]+=1
  CNT[pc+6]-=1
  B[t]=pr*S
 else:
  Z^=ZP[pc+6][t]
  B[t]=pc
 B[f]=0
 if pc==6 or pc==-6:
  KS[si]=t
  if abs(t-f)==2:
   a=f+1 if t>f else f-1
   b=f+3 if t>f else f-4
   B[a]=B[b]
   B[b]=0
   SC+=PSV[4*S+6][a]-PSV[4*S+6][b]
   Z^=ZP[B[a]+6][b]^ZP[B[a]+6][a]
 nc=C&CK[f]&CK[t]
 if nc!=C:
  Z^=ZC[C]^ZC[nc]
  C=nc
 if E!=-1:Z^=ZE[E&7]
 if (pc==1 or pc==-1) and t-f==2*sd:
  E=f+sd
  Z^=ZE[E&7]
 else:E=-1
 H=0 if pc==1 or pc==-1 or cap else H+1
 S=-S
 Z^=ZS
 PATH.append(Z)
 if A(KS[si],S):
  W()
  return False
 return True
def W():
 global S,C,E,H,Z,SC
 m,cap,cs,C,E,H,Z,SC=U.pop()
 f=m&127
 t=m>>7&127
 pr=m>>14&7
 S=-S
 si=S<0
 pc=S if pr else B[t]
 B[f]=pc
 if cs!=t:
  B[cs]=cap
  B[t]=0
 else:B[t]=cap
 if pc==6 or pc==-6:
  KS[si]=f
  if abs(t-f)==2:
   a=f+1 if t>f else f-1
   b=f+3 if t>f else f-4
   B[b]=B[a]
   B[a]=0
 if pr:
  CNT[pr*S+6]-=1
  CNT[S+6]+=1
 if cap:CNT[cap+6]+=1
 PATH.pop()
def G(caps):
 ms=[]
 sd=16*S
 sr=1 if S==1 else 6
 prr=6 if S==1 else 1
 for r in range(8):
  for f in range(8):
   sq=r*16+f
   pc=B[sq]
   if not pc or (pc>0)!=(S==1):continue
   t=pc if pc>0 else -pc
   if t==1:
    to=sq+sd
    if not to&136 and B[to]==0 and (not caps or sq>>4==prr):
     if sq>>4==prr:
      for p in (5,4,3,2):ms.append(sq|to<<7|p<<14)
     else:
      ms.append(sq|to<<7)
      if sq>>4==sr:
       to2=sq+2*sd
       if B[to2]==0:ms.append(sq|to2<<7)
    for to in (sq+sd-1,sq+sd+1):
     if to&136:continue
     q=B[to]
     if q and (q>0)!=(S==1):
      if sq>>4==prr:
       for p in (5,4,3,2):ms.append(sq|to<<7|p<<14)
      else:ms.append(sq|to<<7)
     elif to==E and not q:ms.append(sq|to<<7)
   elif t in (2,6):
    for d in KN if t==2 else KI:
     to=sq+d
     if to&136:continue
     q=B[to]
     if not q or (q>0)!=(S==1):
      if not caps or q:ms.append(sq|to<<7)
    if t==6 and not caps:
     if S==1:
      if C&1 and not B[5] and not B[6] and not A(4,-1) and not A(5,-1) and not A(6,-1):ms.append(4|6<<7)
      if C&2 and not B[3] and not B[2] and not B[1] and not A(4,-1) and not A(3,-1) and not A(2,-1):ms.append(4|2<<7)
     else:
      if C&4 and not B[117] and not B[118] and not A(116,1) and not A(117,1) and not A(118,1):ms.append(116|118<<7)
      if C&8 and not B[115] and not B[114] and not B[113] and not A(116,1) and not A(115,1) and not A(114,1):ms.append(116|114<<7)
   else:
    ds=BD if t==3 else RD if t==4 else BD+RD
    for d in ds:
     to=sq+d
     while not to&136:
      q=B[to]
      if not q:
       if not caps:ms.append(sq|to<<7)
      else:
       if (q>0)!=(S==1):ms.append(sq|to<<7)
       break
      to+=d
 return ms
def L():
 o=[]
 for m in G(False):
  if M(m):
   o.append(m)
   W()
 return o
def V():
 s=SC+30*((CNT[9]>=2)-(CNT[3]>=2))
 ph=min(320*(CNT[8]+CNT[4])+330*(CNT[9]+CNT[3])+500*(CNT[10]+CNT[2])+900*(CNT[11]+CNT[1]),6400)
 r=KS[0]>>4
 f=KS[0]&7
 i=(7-r)*8+f
 s+=(D[320+i]*ph+D[384+i]*(6400-ph))//6400
 r=KS[1]>>4
 f=KS[1]&7
 i=r*8+f
 s-=(D[320+i]*ph+D[384+i]*(6400-ph))//6400
 return s if S==1 else -s
def O(ms,ply,ttm):
 sc=[]
 for m in ms:
  f=m&127
  t=m>>7&127
  pr=m>>14&7
  pc=B[f]
  if m==ttm:s=10000000
  elif pr:s=900000+VAL[pr]
  else:
   cap=B[t]
   v=VAL[abs(cap)] if cap else 100 if t==E and (pc==1 or pc==-1) else 0
   if v:s=1000000+10*v-VAL[abs(pc)]
   elif m==KIL[ply][0]:s=500000
   elif m==KIL[ply][1]:s=400000
   else:s=HST[(pc+6)*128+t]
  sc.append((-s,m))
 sc.sort()
 return [m for _,m in sc]
def Q(a,b,ply):
 global ND,ABT
 ND+=1
 if LIM and ND>=LIM:
  ABT=True
  return 0
 if ply>=120:return V()
 chk=A(KS[0 if S==1 else 1],-S)
 st=V() if not chk else 0
 if not chk:
  if st>=b:return st
  if st>a:a=st
 best=st if not chk else -MATE
 ms=O(G(not chk),ply,0)
 legal=0
 for m in ms:
  if not chk:
   pr=m>>14&7
   if not pr:
    t=m>>7&127
    cap=B[t]
    v=VAL[abs(cap)] if cap else 100 if t==E else 0
    if v and st+v+200<a:continue
  if not M(m):continue
  legal+=1
  sc=-Q(-b,-a,ply+1)
  W()
  if ABT:return 0
  if sc>best:best=sc
  if sc>=b:return sc
  if sc>a:a=sc
 if chk and not legal:return -MATE+ply
 return best
def N(d,a,b,ply):
 global ND,ABT,C,E,H,Z,S
 if ply>0 and (H>=100 or PATH.count(Z)>1):return 0
 if d<=0:return Q(a,b,ply)
 ND+=1
 if LIM and ND>=LIM:
  ABT=True
  return 0
 if ply>=120:return V()
 slot=Z&131071
 ttm=0
 if TTK[slot]==Z:
  ttm=TTM[slot]
  if TTD[slot]>=d:
   s=TTS[slot]
   if s>99000:s-=ply
   elif s<-99000:s+=ply
   fl=TTF[slot]
   if fl==1 or fl==2 and s>=b or fl==3 and s<=a:return s
 chk=A(KS[0 if S==1 else 1],-S)
 a0=a
 if d>=3 and not chk:
  npc=CNT[8]+CNT[9]+CNT[10]+CNT[11] if S==1 else CNT[4]+CNT[3]+CNT[2]+CNT[1]
  if npc:
   st=V()
   if st>=b:
    oC,oE,oH,oZ,oS=C,E,H,Z,S
    if E!=-1:Z^=ZE[E&7]
    E=-1
    H=H+1
    S=-S
    Z^=ZS
    sc=-N(d-3,-b,-b+1,ply+1)
    C,E,H,Z,S=oC,oE,oH,oZ,oS
    if ABT:return 0
    if sc>=b:return sc
 ms=O(G(False),ply,ttm)
 best=-MATE
 bestm=0
 legal=0
 for i,m in enumerate(ms):
  f=m&127
  t=m>>7&127
  pr=m>>14&7
  pc=B[f]
  cap=B[t]
  quiet=not cap and not pr and not (t==E and (pc==1 or pc==-1))
  if not M(m):continue
  legal+=1
  if i==0:sc=-N(d-1,-b,-a,ply+1)
  else:
   rd=d-2 if quiet and i>=2 and d>=3 and not chk else d-1
   sc=-N(rd,-a-1,-a,ply+1)
   if sc>a:sc=-N(d-1,-b,-a,ply+1)
  W()
  if ABT:return 0
  if sc>best:
   best=sc
   bestm=m
  if sc>a:a=sc
  if a>=b:
   if quiet:
    if KIL[ply][0]!=m:
     KIL[ply][1]=KIL[ply][0]
     KIL[ply][0]=m
    HST[(pc+6)*128+t]+=d*d
   break
 if not legal:return -MATE+ply if chk else 0
 TTK[slot]=Z
 TTD[slot]=d
 TTM[slot]=bestm
 s2=best
 if s2>99000:s2+=ply
 elif s2<-99000:s2-=ply
 TTS[slot]=s2
 TTF[slot]=3 if best<=a0 else 2 if best>=b else 1
 return best
def R():
 global ND,ABT,LIM
 ms=L()
 if not ms:return 0
 if len(ms)==1:return ms[0]
 ND=0
 ABT=False
 best=ms[0]
 prev=0
 for d in range(1,65):
  LIM=NODES
  lo=-MATE
  hi=MATE
  g=prev
  sc=N(d,g-1,g,0)
  if ABT:break
  if sc>=g:lo=sc
  else:hi=sc
  while lo<hi-10:
   g=(lo+hi+1)//2
   sc=N(d,g-1,g,0)
   if ABT:break
   if sc>=g:lo=sc
   else:hi=sc
  if ABT:break
  sc=N(d,lo-1,lo,0)
  if ABT:break
  slot=Z&131071
  mv=TTM[slot] if TTK[slot]==Z else 0
  if mv in ms:best=mv
  prev=lo
  if lo>99000:break
 return best
def Y(m):
 f=m&127
 t=m>>7&127
 pr=m>>14&7
 s="abcdefgh"[f&7]+str((f>>4)+1)+"abcdefgh"[t&7]+str((t>>4)+1)
 if pr:s+="  nbrq"[pr]
 return s
def X(u):
 f=(ord(u[1])-49)*16+ord(u[0])-97
 t=(ord(u[3])-49)*16+ord(u[2])-97
 pr="nbrq".index(u[4])+2 if len(u)==5 else 0
 return f|t<<7|pr<<14
def J(fen,gmv):
 F(fen)
 fb=B[:]
 F(START)
 ok=True
 for u in gmv:
  want=X(u)
  if want not in G(False) or not M(want):
   ok=False
   break
 if not ok or B!=fb:F(fen)
 return R()
URL=os.environ.get("MAKEFUN_ENV_URL") or sys.exit("MAKEFUN_ENV_URL is not set")
def P(path,body):
 req=T.Request(URL+path,data=json.dumps(body).encode(),headers={"content-type":"application/json"})
 try:
  with T.urlopen(req,timeout=9) as r:return json.load(r)
 except I.HTTPError as e:return {"_http":e.code,"_body":e.read().decode(errors="replace")}
 except Exception as e:return {"_http":0,"_body":str(e)}
while True:
 g=P("/game",{})
 if g.get("status")=="done":break
 if "_http" in g:
  print("game error",g,file=sys.stderr)
  break
 while g.get("status")=="your_move":
  mv=J(g["fen"],g["moves"])
  g2=P("/move",{"game":g["game"],"move":Y(mv)})
  if "_http" in g2:
   print("move refused",Y(mv),g2,file=sys.stderr)
   for alt in g["legal_moves"]:
    g2=P("/move",{"game":g["game"],"move":alt})
    if "_http" not in g2:break
   else:g2=P("/resign",{"game":g["game"]})
  g=g2
 print(g.get('outcome'),g.get('reason'),file=sys.stderr)
