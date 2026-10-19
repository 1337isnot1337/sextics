#!/usr/bin/env python3
"""Exact degree bounds and finite-field checks for the explicit display clearing.

These are independent algebraic regression checks, not a replacement Lean proof.
"""
import re
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
TEXT = (ROOT/'data/quadric-contact-broken/GenericEliminant.lean').read_text()
EXP = [re.search(r'def eliminantCoeff'+str(i)+r' .*? := (.*)', TEXT)[1].replace('^','**') for i in range(28)]


class Degree:
    def __init__(self, a=0, b=0): self.d=(a,b)
    @staticmethod
    def of(x): return x if isinstance(x,Degree) else Degree()
    def __add__(self,x): return Degree(*map(max,zip(self.d,self.of(x).d)))
    __radd__=__add__
    __sub__=__add__
    __rsub__=__add__
    def __neg__(self): return self
    def __mul__(self,x): return Degree(*(a+b for a,b in zip(self.d,self.of(x).d)))
    __rmul__=__mul__
    def __pow__(self,n): return Degree(*(a*n for a in self.d))


def chart(r,p,q,s,k,u,v):
    h=v-u*r**3; aa=h*h+k*k*r*r*(p*r*r-q*r+s); bb=v+2*u*r**3
    a=2*h*aa; b=k*k*r*(2*h*bb+h*h+k*k*r*r*(s-p*r*r)); c=k**4*r*r*h
    d=aa*aa+2*k**6*r**6; e=2*k*k*r*aa*bb; f=k**4*r*r*(bb*bb+p*k*k*r**4); g=u*k**6*r**6
    L=d*(b*b-a*c)-e*a*b+f*a*a; M=d*b*c-e*a*c+g*a*a
    return h,aa,bb,L,M


env=dict(p=Degree(2,0),q=Degree(1,1),s=Degree(0,2),k=Degree(1,2),u=Degree(6,0),v=Degree(0,6))
assert all(max(eval(e,{'__builtins__':{}},env).d)<=60 for e in EXP)
_,_,_,ld,md=chart(Degree(),**env)
assert max(ld.d+md.d)<=100
assert 26*60+100==1660
assert 27*1660==44820
assert 4*60+44820+3*2+3*27*60==49926
assert max(372+44820,2*2+2*60+44820+60+186)+3*26*60+60==49932
assert 4*49932+2==199730
assert 8*199730==1597840
assert 49926+1597840+27*49932==2995930 < 3000000
assert 3*49926+7*199730+(3*49932+2)+26*49932==2995918 < 3000000

P=65521

def inverse_det(a):
    a=np.array(a,dtype=np.int64)%P; n=len(a); b=np.eye(n,dtype=np.int64); det=1
    for j in range(n):
        pivot=next((i for i in range(j,n) if a[i,j]),None)
        if pivot is None: raise ValueError('Singular test specialization')
        if pivot!=j: a[[pivot,j]]=a[[j,pivot]]; b[[pivot,j]]=b[[j,pivot]]; det=-det
        v=int(a[j,j]); det=det*v%P; iv=pow(v,-1,P);a[j]=a[j]*iv%P;b[j]=b[j]*iv%P
        for i in range(n):
            if i!=j:
                c=a[i,j];a[i]=(a[i]-c*a[j])%P;b[i]=(b[i]-c*b[j])%P
    return b,det


class Mat:
    def __init__(self,a): self.a=np.asarray(a,dtype=np.int64)%P
    @staticmethod
    def of(v): return v if isinstance(v,Mat) else Mat((int(v)%P)*np.eye(27,dtype=np.int64))
    def __add__(self,v): return Mat(self.a+self.of(v).a)
    __radd__=__add__
    def __neg__(self): return Mat(-self.a)
    def __sub__(self,v): return self+-self.of(v)
    def __rsub__(self,v): return self.of(v)+-self
    def __mul__(self,v): return Mat(self.a@v.a) if isinstance(v,Mat) else Mat(self.a*(int(v)%P))
    __rmul__=__mul__
    def __pow__(self,n):
        if n==0:return self.of(1)
        if n<0:return self.inv()**(-n)
        a=self.of(1);b=self
        while n:
            if n&1:a=a*b
            b=b*b;n>>=1
        return a
    def inv(self): return Mat(inverse_det(self.a)[0])
    def det(self): return inverse_det(self.a)[1]
    def adj(self): return self.inv()*self.det()
    def __eq__(self,v): return np.array_equal(self.a,self.of(v).a)


def sources(p,q,s,k,x,y,z,w):
    return [12*x*x*w-12*x*y*z+6*k*x,12*x*y*w-12*y*y*z-6*k*y,2*y*z-2*x*w,
            -2*x*z*w+2*y*z*z+2*k*z+2*p*y-q*x,2*y*z*w-2*x*w*w-2*k*w+q*y-2*s*x,
            (6*x*x+2*p)*(2*x*w+y*z+k)-(6*x*y+q)*(3*x*z),
            (6*x*x+2*p)*(3*y*w)+(6*x*y+q)*(2*x*w+y*z+k)-(6*x*y+q)*(x*w+2*y*z+k)-(6*y*y+2*s)*(3*x*z),
            (6*x*y+q)*(3*y*w)-(6*y*y+2*s)*(x*w+2*y*z+k)]


def numerators(S,T,B,C,k,x,y,z,w):
    nb=y*T+(2*x*w+y*z+k)*B+(3*y*w)*C
    nc=x*T+(3*x*z)*B+(x*w+2*y*z+k)*C
    return [x*nb-y*nc,z*nb-w*nc,nb,-nc]


for alpha,beta in [(1,2),(2,3),(3,1)]:
    p=40*alpha**2%P;q=40*alpha*beta%P;s=40*beta**2%P;k=20*pow(7,-1,P)*alpha*(1+2*beta**2)%P
    u=16*(1+alpha**6)%P;v=16*(1+beta**6)%P;t=pow(u,10,P)*v%P
    co=[eval(e,{'__builtins__':{}},dict(p=p,q=q,s=s,k=k,u=u,v=v))%P for e in EXP]
    arr=np.zeros((27,27),dtype=np.int64);arr[np.arange(1,27),np.arange(26)]=1;arr[:,-1]=-np.array(co[:27])*pow(t,-1,P)%P
    r=Mat(arr);r0=t*r
    h,aa,bb,L,M=chart(r,p,q,s,k,u,v)
    x=-L.inv()*M;y=r*x;z=(aa*x+k*k*r*bb)*((k**3%P)*(r**3)).inv();w=r*z+h*(k*r).inv()
    assert 2*x**3+x*z*z+p*x+u==0 and 2*y**3+y*w*w+s*y+v==0
    L0=pow(t,26,P)*L;M0=pow(t,26,P)*M;delta=L0.det();e0=r0.det();tx=-L0.adj()*M0
    H=pow(t,4,P)*delta*pow(k,3,P)*pow(e0,3,P)%P
    A6=pow(t,6,P)*aa;B3=pow(t,3,P)*bb;h3=pow(t,3,P)*h
    z0=(A6*tx+(k*k*t*t*delta%P)*r0*B3)*r0.adj()**3
    xh=(pow(t,4,P)*pow(k,3,P)*pow(e0,3,P)%P)*tx
    yh=(pow(t,3,P)*pow(k,3,P)*pow(e0,3,P)%P)*r0*tx
    zh=t*z0;wh=r0*z0+(t*t*delta*k*k*e0*e0%P)*h3*r0.adj()
    assert all(a==H*b for a,b in zip([xh,yh,zh,wh],[x,y,z,w]))
    minor=np.array([a.a[:8,0] for a in sources(p,q,s,k,x,y,z,w)])
    mi,md=inverse_det(minor);weights=np.r_[mi[:,3],np.zeros(19,dtype=np.int64)]
    S,T,B,C=2,3,5,7;pole=Mat.of(S)-B*x-C*y;inverse=pole.inv()
    U=numerators(S,T,B,C,k,x,y,z,w)
    def value(a): return int(weights@a.a[:,0])%P
    vg=[value(a*inverse) for a in U]
    gradient=[6*S*S+T*T+p*B*B+q*B*C+s*C*C,2*S*T+k*B*C,S*(2*p*B+q*C)+k*T*C+3*u*B*B,S*(q*B+2*s*C)+k*T*B+3*v*C*C]
    assert sum(a*b for a,b in zip(vg,gradient))%P==T*B%P
    derivativeU=[numerators(*[int(i==j) for i in range(4)],k,x,y,z,w)[j] for j in range(4)]
    poleDerivatives=[Mat.of(1),Mat.of(0),-x,-y]
    assert sum(value(du*inverse-U[j]*inverse*dp*inverse) for j,(du,dp) in enumerate(zip(derivativeU,poleDerivatives)))%P==0
    # The polynomial clearing has exactly the same rational field.
    J0=minor*pow(H,4,P)%P;Ji,E0=inverse_det(J0);w0=np.r_[Ji[:,3]*E0%P,np.zeros(19,dtype=np.int64)]
    Pi=H*pole;Dhat=H*E0*Pi.det()%P
    for i in range(4):
        numerator=pow(H,3,P)*int(w0@(pow(H,3,P)*U[i]*Pi.adj()).a[:,0])%P
        assert numerator*pow(Dhat,-1,P)%P==vg[i]
print('Quadric display clearing: exact degree bounds, line coordinates, rational field, target identity, and divergence checked in three finite-field specializations.')
