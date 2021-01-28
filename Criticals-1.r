#########################################################################################################
# Critical Value simulation Codes of New Combined Threshold Unit Root Test introduced in
# 
# "Threshold Unit Root Tests with Smooth Transitions: A Monte Carlo Study"
# 
# written by 
# 
# Dr. Mehmet ÖZCAN
# mehmetozcan@kmu.edu.tr
#
# *NOTES*
# 1)  Caner & Hansen (2001) Threshold Unit Root test and Threshold Effect test
#     programs are taken from Hansen's web page http://www.ssc.wisc.edu/~bhansen/ .
#     However, unit root test program are adjusted to test unit root null hypothesis 
#     without any deterministic component.
#
# 2)  There are two indicator which come from Caner & Hansen (2001)'s codes. Caner &
#     Hansen investigate different type of threshol variable type and different trimming
#     intervals. In this study, lagged difference threshold variable and [0.15, 0.85] 
#     trimming interval are used for all simulation experiments and empirical application.
#     
#     thresh    Type of threshold variable
#  		  1 for long difference,   z(t-1)=y(t-1)-y(t-(m-1))
#  		  2 for lagged difference, z(t-1)=y(t-m)-y(t-m-1)
#  		  3 for lagged level,      z(t-1)=y(t-m)
#     trim      Trimming Range (normalized threshold, lambda)
#  		  1 for [.15,.85]
#  	 	  2 for [.10,.90]
#  		  3 for [.05,.95]
#     
#    Other important imputs:
#     rep       Monte-Carlo replication 
#     p         Autoregressive Lag Order 
#     mmin      Minimal Delay Order for testing
#     mmax      Maximal Delay Order for testing
#     m		    Delay Order (fixed) for estimation. Set to 0 for m to be estimated by maximizing Wald RT statistics.
#
#
# 3) Results are printed to the screen.
#
# 4) All steps of application process are explained below. Please check them before run the codes.
#
# *Instructions*
#
# 1) First, please install required R packcages stated below.
# 2) Run all codes
#
# 
#    
#
#
#
#########################################################################################################
#########################################################################################################
# Required Packcages 
library(nloptr)
#########################################################################################################
# Required Functions
#########################################################################################################
nulldgp<-function(n){
nn<-n
nt<-as.matrix(rnorm(nn))
nt<-as.matrix(nt-mean(nt))
yt<-nt
for(t in 2:nn) {yt[t]<-yt[t-1]+nt[t]}
yt<-yt
}


# Starting value estimation for LNV(1998) Models (A, B & C) #
startLNV<-function(dta){
tt<-length(dta)
tr<-as.matrix(c(1:tt))
cc<-as.matrix(rep(1,tt))

tauGs<-c()
for(kk in 1:tt){ tauGs[kk]<-(kk/tt) }
gamaGs<-seq(1,10,1)

SSRA<-matrix(0,length(tauGs),length(gamaGs))
SSRB<-matrix(0,length(tauGs),length(gamaGs))
SSRC<-matrix(0,length(tauGs),length(gamaGs))

for(vk in 1:3){
for(vi in 1:(length(gamaGs))){
for(vj in 1:(length(tauGs))){
st<-as.matrix((1/(1+exp(-(gamaGs[vi])*((tr)-(tauGs[vj]*tt))))))
if(vk==1){X<-as.matrix(cbind(cc,st))}
if(vk==2){X<-as.matrix(cbind(cc,tr,st))}
if(vk==3){X<-as.matrix(cbind(cc,tr,st,(tr*st)))} 
XX<-(MASS:::ginv(t(X)%*%X, tol=1e-25))
betas<-XX%*%(t(X)%*%dta)
Yhat<-t((t(betas)%*%t(X)))
ehat<-(dta-Yhat)
if(vk==1){SSRA[vj,vi]<-sum((ehat)^2)}
if(vk==2){SSRB[vj,vi]<-sum((ehat)^2)}
if(vk==3){SSRC[vj,vi]<-sum((ehat)^2)} 
}
}
}

for(vs in 1:3){
if(vs==1){posA<-which(SSRA == min(SSRA), arr.ind = TRUE);
st<-as.matrix((1/(1+exp(-(gamaGs[posA[2]])*((tr)-(tauGs[posA[1]]*tt))))));
X<-as.matrix(cbind(cc,st))}
if(vs==2){posB<-which(SSRB == min(SSRB), arr.ind = TRUE);
st<-as.matrix((1/(1+exp(-(gamaGs[posB[2]])*((tr)-(tauGs[posB[1]]*tt))))));
X<-as.matrix(cbind(cc,tr,st))}
if(vs==3){posC<-which(SSRC == min(SSRC), arr.ind = TRUE);
st<-as.matrix((1/(1+exp(-(gamaGs[posC[2]])*((tr)-(tauGs[posC[1]]*tt))))));
X<-as.matrix(cbind(cc,tr,st,(tr*st)))}

XX<-(MASS:::ginv(t(X)%*%X, tol=1e-25))

if(vs==1){betasA<-XX%*%(t(X)%*%dta);
betasA<-rbind(betasA,gamaGs[posA[2]],tauGs[posA[1]])}
if(vs==2){betasB<-XX%*%(t(X)%*%dta);
betasB<-rbind(betasB,gamaGs[posB[2]],tauGs[posB[1]])}
if(vs==3){betasC<-XX%*%(t(X)%*%dta);
betasC<-rbind(betasC,gamaGs[posC[2]],tauGs[posC[1]])}
}
list(betasA=betasA, betasB=betasB, betasC=betasC)
}

# LNV(1998) Models (A, B & C) Estimation with Sequential Quadratic Programing
estLNV<-function(yt, X, b0a, b0b, b0c){
tt<-length(yt)
stabA<-function(b){sum((yt-(b[1]*X[,1]+b[2]*(1/(1+exp(-(b[3])*((X[,2])-b[4]*tt))))))^2)}
stabB<-function(b){sum((yt-(b[1]*X[,1]+b[2]*X[,2]+b[3]*(1/(1+exp(-(b[4])*((X[,2])-b[5]*tt))))))^2)}
stabC<-function(b){sum((yt-(b[1]*X[,1]+b[2]*X[,2]+b[3]*(1/(1+exp(-(b[5])*((X[,2])-b[6]*tt))))+
b[4]*(X[,2])*(1/(1+exp(-(b[5])*((X[,2])-b[6]*tt))))))^2)}

lba<-c(-Inf,-Inf,0,0)
uba<-c(Inf,Inf,Inf,1)

lbb<-c(-Inf,-Inf,-Inf,0,0)
ubb<-c(Inf,Inf,Inf,Inf,1)

lbc<-c(-Inf,-Inf,-Inf,-Inf,0,0)
ubc<-c(Inf,Inf,Inf,Inf,Inf,1)

SA<-nloptr:::slsqp(b0a,fn=stabA,lower=lba,upper=uba, control=list(xtol_rel=1e-25))
SB<-nloptr:::slsqp(b0b,fn=stabB,lower=lbb,upper=ubb, control=list(xtol_rel=1e-25))
SC<-nloptr:::slsqp(b0c,fn=stabC,lower=lbc,upper=ubc, control=list(xtol_rel=1e-25))

staba<-function(b){(b[1]*X[,1]+b[2]*(1/(1+exp(-(b[3])*((X[,2])-b[4]*tt)))))}
yhatA<-staba(SA$par)

stabb<-function(b){b[1]*X[,1]+b[2]*X[,2]+b[3]*(1/(1+exp(-(b[4])*((X[,2])-b[5]*tt))))}
yhatB<-stabb(SB$par)

stabc<-function(b){(b[1]*X[,1]+b[2]*X[,2]+b[3]*(1/(1+exp(-(b[5])*((X[,2])-b[6]*tt))))+
b[4]*(X[,2])*(1/(1+exp(-(b[5])*((X[,2])-b[6]*tt)))))}
yhatC<-stabc(SC$par)

list(ehat=as.matrix(cbind((yt-yhatA),(yt-yhatB),(yt-yhatC))), yhat=as.matrix(cbind(yhatA,yhatB,yhatC)),BetaA=as.matrix(SA$par),BetaB=as.matrix(SB$par),BetaC=as.matrix(SC$par))
}

# Caner & Hansen (2001) Estimator
tur_est2 <- function(dat,p,mmin,mmax,m,constant,trend){
  t <- nrow(dat)
  n <- t - 1 - p
  mn <- mmax-mmin+1
  ms <- as.matrix(seq(mmin,mn,1))
  dy <- as.matrix(dat[2:t]-dat[1:(t-1)])
  y <- as.matrix(dy[(1+p):(t-1)])
  if(constant==1) x <- matrix(1,n,1)
  if (trend==1) x <- cbind(x,as.matrix(seq(1,n,1)))
  if(constant==1){x <- cbind(x,dat[(1+p):(t-1)],dy[p:(t-2)])}else{
  x <- cbind(dat[(1+p):(t-1)],dy[p:(t-2)])}
  if(p>1) for (ki in 2:p) x <- cbind(x,dy[(p+1-ki):(t-1-ki)])

  if (sum(coef)==0){
      xi_ns <- as.matrix(seq(1,p,1)+1+constant+trend)
        }else{
      idex <- colSums(as.matrix(coef%*%matrix(1,1,p))==(matrix(1,nrow(coef),1)%*%seq(1,p,1)))
      xi_ns <- seq(1,p,1)
      xi_ns <- as.matrix(xi_ns[idex==0]+1+constant+trend)
    }

  if (trend==0){
        if(constant==0){
	        if (sum(coef)==0){
            xi_s <- rbind(1)
                }else{xi_s <- rbind(1,(coef+1))
            }
        }
    }
  if (trend==0){
    if(constant==1){
	if (sum(coef)==0){
      xi_s <- rbind(1,2)
    }else{
      xi_s <- rbind(1,2,(coef+2))
    }
  }
  }
  if (trend==1){
    if(constant==1){
	if (sum(coef)==0){
      xi_s <- rbind(1,2,3)
    }else{
      xi_s <- rbind(1,2,3,(coef+3))
    }
  }
  }

  xs <- as.matrix(x[,xi_s])
  xns <- as.matrix(x[,xi_ns])

  if (thresh==1){
      qs <- dat[(1+p):(t-1)]-dat[(1+p-mmin):(t-1-mmin)]
      qs <- as.matrix(qs)
      if(p>1){
	  for (mi in (mmin+1):mmax){
          qs <- cbind(qs,(dat[(1+p):(t-1)]-dat[(1+p-mi):(t-1-mi)]))
      }
	  }
  }
  if (thresh==2){
      qs <- dat[(1+p-mmin+1):(t-1-mmin+1)]-dat[(1+p-mmin):(t-1-mmin)]
      qs <- as.matrix(qs)
      if(p>1){
	  for (mi in (mmin+1):mmax){
          qs <- cbind(qs,(dat[(1+p-mi+1):(t-1-mi+1)]-dat[(1+p-mi):(t-1-mi)]))
      }
	  }
  }
  if (thresh==3){
      qs <- dat[(1+p-mmin+1):(t-mmin)]
      qs <- as.matrix(qs)
      if(p>1){
	  for (mi in (mmin+1):mmax){
          qs <- cbind(qs,(dat[(1+p-mi+1):(t-mi)]))
      }
	  }
  }
  kx    <- ncol(x)
  ks    <- nrow(coef)+1+constant+trend
  xx    <- solve(t(x)%*%x, tol=1e-25)
  bols  <- xx%*%(t(x)%*%y) 
  eols  <- y - x%*%bols
  sols  <- t(eols)%*%eols
  wwss  <- matrix(0,mn,1)
  smins <- matrix(0,mn,1)
  lams  <- matrix(0,mn,1)
  ws    <- matrix(0,mn,1)
  r1    <- matrix(0,mn,1)
  r2    <- matrix(0,mn,1)
  t1    <- matrix(0,mn,1)
  t2    <- matrix(0,mn,1)
  rur <- rbind(1,(ks+1))+trend+constant
  indx <- 1:(n)
  pi1 <-.2-.05*trim
  pi2 <-.8+.05*trim
  for (mi in 1:mn){
    q <- qs[,mi]
    qq <- unique(q)
    qq <- as.matrix(sort(qq))
    qq <- as.matrix(qq[(floor(n*pi1)+1):(ceiling(n*pi2)-1)])
    qn <- nrow(qq)
    s  <- matrix(0,qn,1)
    wws<- matrix(0,qn,1)
    for (qi in 1:qn){
      d1      <- as.matrix((q<qq[qi]))
      d2      <- 1-d1
      xz      <- cbind((xs*(d1%*%matrix(1,1,ncol(xs)))),(xs*(d2%*%matrix(1,1,ncol(xs)))),xns)
      xxi     <- solve(t(xz)%*%xz, tol=1e-25)
      bthresh <- xxi%*%(t(xz)%*%y)
      e       <- y-xz%*%bthresh
      s[qi]   <- t(e)%*%e
      v       <- xxi*as.vector((t(e)%*%e)/(n-kx-ks))
      vd      <- diag(v)
      ts      <- as.matrix(bthresh[rur]/sqrt(vd[rur]))
      wws[qi] <- t(ts)%*%ts
    }
    qi         <- which.max(wws)
    lam        <- qq[qi]
    smin       <- s[qi]
    wwsmax     <- wws[qi]
    ws[mi]     <- (n-kx-ks)*(sols-smin)/smin
    smins[mi]  <- smin
    lams[mi]   <- lam
    wwss[mi]   <- wwsmax
    d1         <- as.matrix((q<lam))
    d2         <- 1-d1
    xz         <- cbind((xs*(d1%*%matrix(1,1,ncol(xs)))),(xs*(d2%*%matrix(1,1,ncol(xs)))),xns)
    mmi        <- solve(t(xz)%*%xz, tol=1e-25)
    bthresh    <- mmi%*%(t(xz)%*%y)
    e          <- y - xz%*%bthresh
    v          <- mmi*as.vector((t(e)%*%e)/(n-kx-ks))
    vd         <- diag(v)
    ts         <- as.matrix(bthresh[rur]/sqrt(vd[rur]))
    r1[mi]     <- t(ts^2)%*%(ts<0)
    r2[mi]     <- t(ts)%*%ts
    t1[mi]     <- -ts[1]
    t2[mi]     <- -ts[2]
  }
  if (m != 0) {mi <- m-mmin+1}else{mi<- which.max(wwss)}
  mhat     <- ms[mi]
  w        <- ws[mi]
  lam      <- lams[mi]
  q        <- qs[,mi]
  d1       <- as.matrix((q<lam))
  d2       <- 1-d1
  xz       <- cbind((xs*(d1%*%matrix(1,1,ncol(xs)))),(xs*(d2%*%matrix(1,1,ncol(xs)))),xns)
  mmi      <- solve(t(xz)%*%xz, tol=1e-25)
  bthresh  <- mmi%*%(t(xz)%*%y)
  e        <- y - xz%*%bthresh
  ee       <- t(e)%*%e
  v        <- mmi*as.vector((ee)/(n-kx-ks))
  vd       <- diag(v)
  v1       <- vd[1:ks]
  v2       <- vd[(ks+1):(2*ks)]
  b1       <- bthresh[1:ks]
  b2       <- bthresh[(ks+1):(2*ks)]
  ts       <- as.matrix(((b1-b2)^2)/(v1+v2))
  bs_s     <- cbind(b1,sqrt(v1),matrix(0,ks,1),b2,sqrt(v2))
  bs_ns    <- cbind(bthresh[(1+2*ks):(kx+ks)],sqrt(vd[(1+2*ks):(kx+ks)]))
  ar01     <-bthresh[(2+constant+trend):(ks)]
  ar02     <-bthresh[(2+constant+trend+ks):(ks*2)]
  leng     <-sum(x[,ncol(x)]>lam)
list(mhat=mhat,lam=lam,e=e,bs_s=bs_s,ar01=ar01,ar02=ar02,b1=b1,b2=b2,r1=r1,r2=r2,t1=t1,t2=t2,ts=ts,ws=ws,w=w,
wws=wws, wwss=wwss,leng=leng,vd=vd)
}

# Simulation Settings
#########################################################################################################

rep      <- 10000
n        <- 100
p        <- 1
crlevel01 <- 0.99
crlevel05 <- 0.95
crlevel10 <- 0.90

thresh   <- 2 #
trim     <- 1 #
m        <- 0
mmin     <- 1
mmax     <- p
coef     <- matrix(c(1:p),p,1)

tr<-as.matrix(c(1:n))
cc<-as.matrix(rep(1,n))

ptm <- proc.time()
set.seed(012345)

RTDist <- matrix(0,rep,6)

for(i in 1:rep){
yt   <- as.matrix(nulldgp(n))
LNV  <- startLNV(yt)
b0a  <- LNV$betasA
b0b  <- LNV$betasB
b0c  <- LNV$betasC
X    <- as.matrix(cbind(cc,tr))
ELNV <- estLNV(yt, X, b0a, b0b,b0c)
D    <- as.matrix(ELNV$ehat)

tarA <- tur_est2(as.matrix(D[,1]),p,mmin,mmax,m,0,0);
tarB <- tur_est2(as.matrix(D[,2]),p,mmin,mmax,m,0,0);
tarC <- tur_est2(as.matrix(D[,3]),p,mmin,mmax,m,0,0);

RTDist[i,1] <- tarA$r1[tarA$mhat]
RTDist[i,2] <- tarB$r1[tarB$mhat]
RTDist[i,3] <- tarC$r1[tarC$mhat]
RTDist[i,4] <- tarA$r2[tarA$mhat]
RTDist[i,5] <- tarB$r2[tarB$mhat]
RTDist[i,6] <- tarC$r2[tarC$mhat]
}

RTDist<-apply(RTDist,2,sort)

CR      <- matrix(0,3,6)
for(i in 1:3){
if(i==1) crt <- 0.90
if(i==2) crt <- 0.95
if(i==3) crt <- 0.99
CR[i,1] <- RTDist[,1][round(rep*crt)]
CR[i,2] <- RTDist[,4][round(rep*crt)]
CR[i,3] <- RTDist[,2][round(rep*crt)]
CR[i,4] <- RTDist[,5][round(rep*crt)]
CR[i,5] <- RTDist[,3][round(rep*crt)]
CR[i,6] <- RTDist[,6][round(rep*crt)]
}
proc.time() - ptm
printres <- function(CR){
cat ("\n")
cat ("Critical Values for Selected Sample Size"                                           , "\n")
cat ("Number of Observations (T):", n                                                     , "\n")
cat ("\n")
cat ("Model A"                                                                            , "\n")
cat ("   ","R1t", "     R2t"                                                              , "\n")
cat ("10%", CR[1,1], CR[1,2]                                                              , "\n")
cat (" 5%", CR[2,1], CR[2,2]                                                              , "\n")
cat (" 1%", CR[3,1], CR[3,2]                                                              , "\n")
cat ("\n")
cat ("Model B"                                                                            , "\n")
cat ("   ","R1t", "     R2t"                                                              , "\n")
cat ("10%", CR[1,3], CR[1,4]                                                              , "\n")
cat (" 5%", CR[2,3], CR[2,4]                                                              , "\n")
cat (" 1%", CR[3,3], CR[3,4]                                                              , "\n")
cat ("\n")
cat ("Model C"                                                                            , "\n")
cat ("   ","R1t", "     R2t"                                                              , "\n")
cat ("10%", CR[1,5], CR[1,6]                                                              , "\n")
cat (" 5%", CR[2,5], CR[2,6]                                                              , "\n")
cat (" 1%", CR[3,5], CR[3,6]                                                              , "\n")
cat ("\n")
}

printres(CR)
# END #
