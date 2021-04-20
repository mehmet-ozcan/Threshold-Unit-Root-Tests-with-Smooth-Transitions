#########################################################################################################
# Empirical Application Codes of
# 
# "Threshold Unit Root Tests with Smooth Transitions"
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
# 3) Results are printed to the screen.
#
# 4) All steps of application process are explained below. Please check them before run the codes.
#
# *Instructions*
#
# 1) First, please install required R packcages stated in PART-1
# 2) Run all codes in PART-1
# 3) Before run PART-2, please chose working directory folder that contains your "data.txt" file.
# 4) PART-2 codes analyse both the USA's and Turkey's data. Threfore, before analyse your data try
#    data of this study. It could be found at "data.txt" file in same repository of Dr. Özcan's GitHub page.
#
#
#
#########################################################################################################
# PART -1 
#########################################################################################################
# Required Packcages 
library(nloptr)
library(zoo)
# Required Functions
#########################################################################################################
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
#########################################################################################################
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
#########################################################################################################
# ADF Estimator
linear<-function(dat,p,cons,trend){
    t <- nrow(dat)
    n <- t - 1 - p
    dy <- as.matrix(dat[2:t]-dat[1:(t-1)])
    y  <- as.matrix(dy[(1+p):(t-1)])
    x  <- cbind(dat[(1+p):(t-1)], dy[p:(t-2)])

    if(p>=2){for (k in 2:p) x <- cbind(x,dy[(p+1-k):(t-1-k)])}
    if(cons==1 & trend==0)  x <- cbind(rep(1,n), x)
    if(cons==1 & trend==1)  x <- cbind(rep(1,n),seq(1,n,1),x)

    kx     <- ncol(x)
    xx     <- solve(t(x)%*%x, tol=1e-25)
    bols   <- xx%*%(t(x)%*%y) 
    eols   <- y - x%*%bols
    sols   <- t(eols)%*%eols
    sigols <- sols/(n-kx)
    seols  <- sqrt(diag(xx)%*%sigols)
    rho    <- bols[1+cons+trend]
    tadf   <- rho/seols[1+cons+trend]
    ar0    <- as.matrix(bols[(cons+trend+2):(cons+trend+1+p)])
    bic<-log((sum(eols^2))/t)+(length(bols)*(log(t)/t))
    aic<-log((sum(eols^2))/t)+(length(bols)*(2/t))
    list(ar0=ar0,eols=eols,aic=aic,bic=bic,tadf=tadf,rho=rho)
}
#########################################################################################################
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
# Caner & Hansen (2001) Threshold Effect Wald Test Bootstrap p-values
pvWald<-function(dat,p,ar0,eols,rho,boot,w){
t <- nrow(dat)
n <- t - 1 - p
y0 <- dat-mean(dat)
y0 <- as.matrix(y0[1:(1+p)])
aa <- matrix(0,p+1,1)
aa[1] <- 1 + rho
aa[1:p] <- aa[1:p] + ar0
aa[2:(p+1)] <- aa[2:(p+1)] - ar0
bootw <- matrix(0,boot,1)
for (ib in 1:boot){
    eols_c <- as.matrix(eols[ceiling(runif(t)*n)])
    datb <- y0
for (i in (nrow(y0)+1):(nrow(eols_c))){
        datbb <- eols_c[i]
        for (j in 1:nrow(y0)) datbb <- datbb + aa[j]*datb[(i-j)]
        datb <- rbind(datb,datbb)
    }
out       <- tur_est2(datb,p,1,p,0,0,0) 
bootw[ib] <- out$w
}
pw <- mean(bootw > w)
cbind(w,pw)
}

#########################################################################################################
# 5% Criticals T=200
R1A <- 20.82907
R2A <- 21.07073
R1B <- 26.67934
R2B <- 26.80033
R1C <- 29.65022
R2C <- 29.69269
LNVa<- -4.161
LNVb<- -4.629
LNVc<- -4.867
ADFm<- -2.8759 
ADFt<- -3.4326 # MacKinnon (1991) based Critical value

#########################################################################################################
# PART - 2
#########################################################################################################
# Aplication
# select working directory file.
# setwd("your folder directory") 
# read data
D   <- read.table("data.txt")
tri <- D[,1]
usi <- D[,2]
# logarithms
tri <-as.matrix(log(tri))
usi <-as.matrix(log(usi))
# estimation parameter of LNV smooth transition functions 
tr    <-as.matrix(c(1:length(tri)))
cc    <-as.matrix(rep(1,length(tri)))
X     <-as.matrix(cbind(cc,tr))
SLNVtr<- startLNV(tri)
SLNVus<- startLNV(usi)
b0atr <- SLNVtr$betasA; b0btr  <- SLNVtr$betasB; b0ctr  <- SLNVtr$betasC
b0aus <- SLNVus$betasA; b0bus  <- SLNVus$betasB; b0cus  <- SLNVus$betasC

ELNVtr<- estLNV(tri, X, b0atr, b0btr, b0ctr)
ELNVus<- estLNV(usi, X, b0aus, b0bus, b0cus)
Ytr   <- as.matrix(ELNVtr$yhat)
Yus   <- as.matrix(ELNVus$yhat)
Dtr   <- as.matrix(ELNVtr$ehat)
Dus   <- as.matrix(ELNVus$ehat)
# plots
# TR
par(mfrow=c(3,1))
plot(ts(Ytr[,1], start=c(2004,1),frequency=12),lty=2,axes=FALSE,lwd=2,col="black",ylab=NA,xlab="Years",main="Model A",ylim=c(min(tri),max(tri)))
mtext(side=3,text=paste("industrial production and fitted smooth transition for Turkey"),line=2.5,lwd=2,cex=1)
lines(ts(tri, start=c(2004,1), frequency=12),lty=1, lwd=2, col="gray42")
axis(1, at=c(2004:2020), labels=c(2004:2020),las=3, gap.axis=0.1)
axis(2, at = seq(round(min(tri),1),round(max(tri),1),0.1),lwd=1.5)
abline(v=(seq(2004,2020,1)), col="lightgray", lty="dotted")
abline(h=seq(round(min(tri),1),round(max(tri),1),0.1), col="lightgray", lty="dotted")
plot(ts(Ytr[,2], start=c(2004,1),frequency=12),lty=2,axes=FALSE,lwd=2,col="black",ylab=NA,xlab="Years",main="Model B",ylim=c(min(tri),max(tri)))
lines(ts(tri, start=c(2004,1), frequency=12),lty=1, lwd=2, col="gray42")
axis(1, at=c(2004:2020), labels=c(2004:2020),las=3, gap.axis=0.1)
axis(2, at = seq(round(min(tri),1),round(max(tri),1),0.1),lwd=1.5)
abline(v=(seq(2004,2020,1)), col="lightgray", lty="dotted")
abline(h=seq(round(min(tri),1),round(max(tri),1),0.1), col="lightgray", lty="dotted")
plot(ts(Ytr[,3], start=c(2004,1),frequency=12),lty=2,axes=FALSE,lwd=2,col="black",ylab=NA,xlab="Years",main="Model C",ylim=c(min(tri),max(tri)))
lines(ts(tri, start=c(2004,1), frequency=12),lty=1, lwd=2, col="gray42")
axis(1, at=c(2004:2020), labels=c(2004:2020),las=3, gap.axis=0.1)
axis(2, at = seq(round(min(tri),1),round(max(tri),1),0.1),lwd=1.5)
abline(v=(seq(2004,2020,1)), col="lightgray", lty="dotted")
abline(h=seq(round(min(tri),1),round(max(tri),1),0.1), col="lightgray", lty="dotted")

# US
par(mfrow=c(3,1))
plot(ts(Yus[,1], start=c(2004,1),frequency=12),lty=2,axes=FALSE,lwd=2,col="black",ylab=NA,xlab="Years",main="Model A",ylim=c(min(usi),max(usi)))
mtext(side=3,text=paste("industrial production and fitted smooth transition for USA"),line=2.5,lwd=2,cex=1)
lines(ts(usi, start=c(2004,1), frequency=12),lty=1, lwd=2, col="gray42")
axis(1, at=c(2004:2020), labels=c(2004:2020),las=3, gap.axis=0.1)
axis(2, at = seq(round(min(usi),1),round(max(usi),1),0.1),lwd=1.5)
abline(v=(seq(2004,2020,1)), col="lightgray", lty="dotted")
abline(h=seq(round(min(usi),1),round(max(usi),1),0.1), col="lightgray", lty="dotted")
plot(ts(Yus[,2], start=c(2004,1),frequency=12),lty=2,axes=FALSE,lwd=2,col="black",ylab=NA,xlab="Years",main="Model B",ylim=c(min(usi),max(usi)))
lines(ts(usi, start=c(2004,1), frequency=12),lty=1, lwd=2, col="gray42")
axis(1, at=c(2004:2020), labels=c(2004:2020),las=3, gap.axis=0.1)
axis(2, at = seq(round(min(usi),1),round(max(usi),1),0.1),lwd=1.5)
abline(v=(seq(2004,2020,1)), col="lightgray", lty="dotted")
abline(h=seq(round(min(usi),1),round(max(usi),1),0.1), col="lightgray", lty="dotted")
plot(ts(Yus[,3], start=c(2004,1),frequency=12),lty=2,axes=FALSE,lwd=2,col="black",ylab=NA,xlab="Years",main="Model C",ylim=c(min(usi),max(usi)))
lines(ts(usi, start=c(2004,1), frequency=12),lty=1, lwd=2, col="gray42")
axis(1, at=c(2004:2020), labels=c(2004:2020),las=3, gap.axis=0.1)
axis(2, at = seq(round(min(usi),1),round(max(usi),1),0.1),lwd=1.5)
abline(v=(seq(2004,2020,1)), col="lightgray", lty="dotted")
abline(h=seq(round(min(usi),1),round(max(usi),1),0.1), col="lightgray", lty="dotted")

# Extraction of Estimated Data
# write.table(as.matrix(cbind(tri,Ytr[,1],Ytr[,2],Ytr[,3])),"TRest.txt",row.names=FALSE,col.names=FALSE)
# write.table(as.matrix(cbind(usi,Yus[,1],Yus[,2],Yus[,3])),"USest.txt",row.names=FALSE,col.names=FALSE)

# ADF Test
maxp<- 10
BIC <- matrix(0,maxp,2) 
for(i in 1:maxp){
adftr <- linear(as.matrix(tri),i,1,1)
adfus <- linear(as.matrix(usi),i,1,1)
BIC[i,1]<-adftr$bic
BIC[i,2]<-adfus$bic
}
ptr <- which.min(BIC[,1])
pus <- which.min(BIC[,2])

adftr0 <- linear(as.matrix(tri),ptr,1,1)
adfus0 <- linear(as.matrix(usi),pus,1,1)

# LNV Test
BICL <- matrix(0,maxp,6) 
for(i in 1:maxp){
adftra <- linear(as.matrix(Dtr[,1]),i,1,1)
adftrb <- linear(as.matrix(Dtr[,2]),i,1,1)
adftrc <- linear(as.matrix(Dtr[,3]),i,1,1)

adfusa <- linear(as.matrix(Dus[,1]),i,1,1)
adfusb <- linear(as.matrix(Dus[,2]),i,1,1)
adfusc <- linear(as.matrix(Dus[,3]),i,1,1)

BICL[i,1]<-adftra$bic; BICL[i,2]<-adftrb$bic; BICL[i,3]<-adftrc$bic;
BICL[i,4]<-adfusa$bic; BICL[i,5]<-adfusb$bic; BICL[i,6]<-adfusc$bic
}
ptra <- which.min(BICL[,1]); ptrb <- which.min(BICL[,2]); ptrc <- which.min(BICL[,3]);
pusa <- which.min(BICL[,4]); pusb <- which.min(BICL[,5]); pusc <- which.min(BICL[,6]);
PLNV <-cbind(ptra,ptrb,ptrc,pusa,pusb,pusc)

adftrA <- linear(as.matrix(Dtr[,1]),ptra,1,1)
adftrB <- linear(as.matrix(Dtr[,2]),ptrb,1,1)
adftrC <- linear(as.matrix(Dtr[,3]),ptrc,1,1)

adfusA <- linear(as.matrix(Dus[,1]),pusa,1,1)
adfusB <- linear(as.matrix(Dus[,2]),pusb,1,1)
adfusC <- linear(as.matrix(Dus[,3]),pusc,1,1)

# Caner & Hansen (2001) Test with Smooth Transition
# Caner & Hansen (2001) TAR Model Estimation Settings 
thresh   <- 2 
trim     <- 1 
#
MAXR <- matrix(0,maxp,6)
for(i in 1:maxp){
coef   <- matrix(c(1:i),i,1)
tarAtr <-tur_est2(as.matrix(Dtr[,1]),i,1,i,0,0,0)
tarBtr <-tur_est2(as.matrix(Dtr[,2]),i,1,i,0,0,0)
tarCtr <-tur_est2(as.matrix(Dtr[,3]),i,1,i,0,0,0)

tarAus <-tur_est2(as.matrix(Dus[,1]),i,1,i,0,0,0)
tarBus <-tur_est2(as.matrix(Dus[,2]),i,1,i,0,0,0)
tarCus <-tur_est2(as.matrix(Dus[,3]),i,1,i,0,0,0)

MAXR[i,1]<-tarAtr$r1[tarAtr$mhat]; MAXR[i,2]<-tarBtr$r1[tarBtr$mhat]; MAXR[i,3]<-tarCtr$r1[tarCtr$mhat];
MAXR[i,4]<-tarAus$r1[tarAus$mhat]; MAXR[i,5]<-tarBus$r1[tarBus$mhat]; MAXR[i,6]<-tarCus$r1[tarCus$mhat]
}
ptrA <- which.max(MAXR[,1]); ptrB <- which.max(MAXR[,2]); ptrC <- which.max(MAXR[,3]);
pusA <- which.max(MAXR[,4]); pusB <- which.max(MAXR[,5]); pusC <- which.max(MAXR[,6]);
PLCH <- cbind(ptrA,ptrB,ptrC,pusA,pusB,pusC)

coef   <- matrix(c(1:ptrA),ptrA,1)
tartrA <- tur_est2(as.matrix(Dtr[,1]),ptrA,1,ptrA,0,0,0)
coef   <- matrix(c(1:ptrB),ptrB,1)
tartrB <- tur_est2(as.matrix(Dtr[,2]),ptrB,1,ptrB,0,0,0)
coef   <- matrix(c(1:ptrC),ptrC,1)
tartrC <- tur_est2(as.matrix(Dtr[,3]),ptrC,1,ptrC,0,0,0)

coef   <- matrix(c(1:pusA),pusA,1)
tarusA <- tur_est2(as.matrix(Dus[,1]),pusA,1,pusA,0,0,0)
coef   <- matrix(c(1:pusB),pusB,1)
tarusB <- tur_est2(as.matrix(Dus[,2]),pusB,1,pusB,0,0,0)
coef   <- matrix(c(1:pusC),pusC,1)
tarusC <- tur_est2(as.matrix(Dus[,3]),pusC,1,pusC,0,0,0)

# Caner & Hansen (2001) Threshold Effect test statistics and p-values #
set.seed(12345)
boot<-1000
# Turkey
coef    <- matrix(c(1:ptrA),ptrA,1)
lnWAtr  <- linear(as.matrix(Dtr[,1]),ptrA,0,0)
pvalAtr <- pvWald(as.matrix(Dtr[,1]),ptrA,lnWAtr$ar0,lnWAtr$eols,lnWAtr$rho,boot,tartrA$w)
coef    <- matrix(c(1:ptrB),ptrB,1)
lnWBtr  <- linear(as.matrix(Dtr[,2]),ptrB,0,0)
pvalBtr <- pvWald(as.matrix(Dtr[,2]),ptrB,lnWBtr$ar0,lnWBtr$eols,lnWBtr$rho,boot,tartrB$w)
coef    <- matrix(c(1:ptrC),ptrC,1)
lnWCtr  <- linear(as.matrix(Dtr[,3]),ptrC,0,0)
pvalCtr <- pvWald(as.matrix(Dtr[,3]),ptrC,lnWCtr$ar0,lnWCtr$eols,lnWCtr$rho,boot,tartrC$w)
# USA
coef    <- matrix(c(1:pusA),pusA,1)
lnWAus  <- linear(as.matrix(Dus[,1]),pusA,0,0)
pvalAus <- pvWald(as.matrix(Dus[,1]),pusA,lnWAus$ar0,lnWAus$eols,lnWAus$rho,boot,tarusA$w)
coef    <- matrix(c(1:pusB),pusB,1)
lnWBus  <- linear(as.matrix(Dus[,2]),pusB,0,0)
pvalBus <- pvWald(as.matrix(Dus[,2]),pusB,lnWBus$ar0,lnWBus$eols,lnWBus$rho,boot,tarusB$w)
coef    <- matrix(c(1:pusC),pusC,1)
lnWCus  <- linear(as.matrix(Dus[,3]),pusC,0,0)
pvalCus <- pvWald(as.matrix(Dus[,3]),pusC,lnWCus$ar0,lnWCus$eols,lnWCus$rho,boot,tarusC$w)


# Tables
trit<-ts(diff(tri,1),start<-c(2004,2),frequency=12)
usit<-ts(diff(usi,1),start<-c(2004,2),frequency=12)
ntr <-length(tri)
nus <-length(usi)
printlog<-function(tri,usi){
cat ("\n")
cat ("Parameter Estimation Result of Smooth Transition for Industrial Production Index of Turkey" , "\n")
cat ("Number of Observations:", ntr                                                               , "\n")
cat ("Optimization          : Sequential Quadratic Programming"                                   , "\n")
cat ("\n")
cat ("Model A"                                                                                    , "\n")
cat ("Mid Point Date"                                                                             , "\n")
cat ("--------------"                                                                             , "\n")
print(as.yearmon(time(trit))[round((ELNVtr$BetaA[4]*ntr))])
cat ("Mid Point Tau               :", ELNVtr$BetaA[4]                                             , "\n")
cat ("Speed of Transition Gamma   :", ELNVtr$BetaA[3]                                             , "\n")
cat ("\n")
cat ("Model B"                                                                                    , "\n")
cat ("Mid Point Date"                                                                             , "\n")
cat ("--------------"                                                                             , "\n")
print(as.yearmon(time(trit))[round((ELNVtr$BetaB[5]*ntr))])
cat ("Mid Point Tau               :", ELNVtr$BetaB[5]                                             , "\n")
cat ("Speed of Transition Gamma   :", ELNVtr$BetaB[4]                                             , "\n")
cat ("\n")
cat ("Model C"                                                                                    , "\n")
cat ("Mid Point Date"                                                                             , "\n")
cat ("--------------"                                                                             , "\n")
print(as.yearmon(time(trit))[round((ELNVtr$BetaC[6]*ntr))])
cat ("Mid Point Tau               :", ELNVtr$BetaC[6]                                             , "\n")
cat ("Speed of Transition Gamma   :", ELNVtr$BetaC[5]                                             , "\n")
cat ("\n")
cat ("*******************************************************************************************", "\n")
cat ("\n")
cat ("Parameter Estimation Result of Smooth Transition for Industrial Production Index of USA"    , "\n")
cat ("Number of Observations:", nus                                                               , "\n")
cat ("Optimization          : Sequential Quadratic Programming"                                   , "\n")
cat ("\n")
cat ("Model A"                                                                                    , "\n")
cat ("Mid Point Date"                                                                             , "\n")
cat ("--------------"                                                                             , "\n")
print(as.yearmon(time(usit))[round((ELNVus$BetaA[4]*nus))])
cat ("Mid Point Tau               :", ELNVus$BetaA[4]                                             , "\n")
cat ("Speed of Transition Gamma   :", ELNVus$BetaA[3]                                             , "\n")
cat ("\n")
cat ("Model B"                                                                                    , "\n")
cat ("Mid Point Date"                                                                             , "\n")
cat ("--------------"                                                                             , "\n")
print(as.yearmon(time(usit))[round((ELNVus$BetaB[5]*nus))])
cat ("Mid Point Tau               :", ELNVus$BetaB[5]                                             , "\n")
cat ("Speed of Transition Gamma   :", ELNVus$BetaB[4]                                             , "\n")
cat ("\n")
cat ("Model C"                                                                                    , "\n")
cat ("Mid Point Date"                                                                             , "\n")
cat ("--------------"                                                                             , "\n")
print(as.yearmon(time(usit))[round((ELNVus$BetaC[6]*nus))])
cat ("Mid Point Tau               :", ELNVus$BetaC[6]                                             , "\n")
cat ("Speed of Transition Gamma   :", ELNVus$BetaC[5]                                             , "\n")
cat ("\n")
cat ("*******************************************************************************************", "\n")
cat ("\n")
}

printadf<-function(tri,usi,ptr,pus){
cat ("\n")
cat ("ADF Results for Industrial Production Index of Turkey" , "\n")
cat ("Number of Observations:", length(tri)                  , "\n")
cat ("Selected Optimal Lag  :", ptr, "\n")
cat ("Information Criteria  : BIC"                           , "\n")
cat ("Model Type            : Constant & Trend"              , "\n")
cat ("Test Statistics       :", adftr0$tadf                  , "\n")
cat ("5% Critical Value     :",ADFt                          , "\n")
cat ("\n")
cat ("ADF Results for Industrial Production Index of USA"    , "\n")
cat ("Number of Observations:", length(usi)                  , "\n")
cat ("Selected Optimal Lag  :", pus, "\n")
cat ("Information Criteria  : BIC"                           , "\n")
cat ("Model Type            : Constant & Trend"              , "\n")
cat ("Test Statistics       :", adfus0$tadf                  , "\n")
cat ("5% Critical Value     :",ADFt                          , "\n")
}

printlnv<-function(tri,usi,PLNV){
cat ("\n")
cat ("LNV Results for Industrial Production Index of Turkey" , "\n")
cat ("Number of Observations:", length(tri)                  , "\n")
cat ("\n")
cat ("Model A"                                               , "\n")
cat ("Selected Optimal Lag  :", PLNV[1]                      , "\n")
cat ("Information Criteria  : BIC"                           , "\n")
cat ("Test Statistics       :", adftrA$tadf                  , "\n")
cat ("5% Critical Value     :", LNVa                         , "\n")
cat ("\n")
cat ("Model B"                                               , "\n")
cat ("Selected Optimal Lag  :", PLNV[2]                      , "\n")
cat ("Information Criteria  : BIC"                           , "\n")
cat ("Test Statistics       :", adftrB$tadf                  , "\n")
cat ("5% Critical Value     :", LNVb                         , "\n")
cat ("\n")
cat ("Model C"                                               , "\n")
cat ("Selected Optimal Lag  :", PLNV[3]                      , "\n")
cat ("Information Criteria  : BIC"                           , "\n")
cat ("Test Statistics       :", adftrC$tadf                  , "\n")
cat ("5% Critical Value     :", LNVc                         , "\n")
cat ("\n")
cat ("******************************************************", "\n")
cat ("\n")
cat ("LNV Results for Industrial Production Index of USA" , "\n")
cat ("Number of Observations:", length(usi)                  , "\n")
cat ("\n")
cat ("Model A"                                               , "\n")
cat ("Selected Optimal Lag  :", PLNV[4]                      , "\n")
cat ("Information Criteria  : BIC"                           , "\n")
cat ("Test Statistics       :", adfusA$tadf                  , "\n")
cat ("5% Critical Value     :", LNVa                         , "\n")
cat ("\n")
cat ("Model B"                                               , "\n")
cat ("Selected Optimal Lag  :", PLNV[5]                      , "\n")
cat ("Information Criteria  : BIC"                           , "\n")
cat ("Test Statistics       :", adfusB$tadf                  , "\n")
cat ("5% Critical Value     :", LNVb                         , "\n")
cat ("\n")
cat ("Model C"                                               , "\n")
cat ("Selected Optimal Lag  :", PLNV[6]                      , "\n")
cat ("Information Criteria  : BIC"                           , "\n")
cat ("Test Statistics       :", adfusC$tadf                  , "\n")
cat ("5% Critical Value     :", LNVc                         , "\n")
cat ("\n")
}

printlch<-function(tri,usi,PLCH){
cat ("\n")
cat ("New Combined Caner & Hansen (2001) Results for Industrial Production Index of Turkey"            , "\n")
cat ("Number of Observations:", length(tri)                                                            , "\n")
cat ("\n")
cat ("Model A"                                                                                         , "\n")
cat ("Selected Optimal Lag :",PLCH[1]                                                                  , "\n")
cat ("Information Criteria : Superme RT"                                                               , "\n")
cat ("R1 Test Statistics   :",tartrA$r1[tartrA$mhat],"  / R2 Test Statistics   :",tartrA$r2[tartrA$mhat] , "\n")
cat ("R1 5% Critical Value :",R1A                   ,"/ R2 5% Critical Value :",R2A                    , "\n")
cat ("++++++++++++++++++++++"                                                                          , "\n")
cat ("Caner & Hansen (2001) Threshold Effect Wald Test"                                                , "\n")
cat ("Test Statistics      :",pvalAtr[1]                                                               , "\n")
cat ("Bootstrap p-value    :",pvalAtr[2]                                                               , "\n")
cat ("\n")
cat ("Model B"                                                                                         , "\n")
cat ("Selected Optimal Lag :",PLCH[2]                                                                  , "\n")
cat ("Information Criteria : Superme RT"                                                               , "\n")
cat ("R1 Test Statistics   :",tartrB$r1[tartrB$mhat],"/ R2 Test Statistics   :",tartrB$r2[tartrB$mhat] , "\n")
cat ("R1 5% Critical Value :",R1B                   ,"/ R2 5% Critical Value :",R2B                    , "\n")
cat ("++++++++++++++++++++++"                                                                          , "\n")
cat ("Caner & Hansen (2001) Threshold Effect Wald Test"                                                , "\n")
cat ("Test Statistics      :",pvalBtr[1]                                                               , "\n")
cat ("Bootstrap p-value    :",pvalBtr[2]                                                               , "\n")
cat ("\n")
cat ("Model C"                                                                                         , "\n")
cat ("Selected Optimal Lag :",PLCH[3]                                                                  , "\n")
cat ("Information Criteria : Superme RT"                                                               , "\n")
cat ("R1 Test Statistics   :",tartrC$r1[tartrC$mhat],"/ R2 Test Statistics   :",tartrC$r2[tartrC$mhat] , "\n")
cat ("R1 5% Critical Value :",R1C                   ,"/ R2 5% Critical Value :",R2C                    , "\n")
cat ("++++++++++++++++++++++"                                                                          , "\n")
cat ("Caner & Hansen (2001) Threshold Effect Wald Test"                                                , "\n")
cat ("Test Statistics      :",pvalCtr[1]                                                               , "\n")
cat ("Bootstrap p-value    :",pvalCtr[2]                                                               , "\n")
cat ("\n")
cat ("************************************************************************************************", "\n")
cat ("\n")
cat ("New Combined Caner & Hansen (2001) Results for Industrial Production Index of USA"               , "\n")
cat ("Number of Observations:", length(usi)                                                            , "\n")
cat ("\n")
cat ("Model A"                                                                                         , "\n")
cat ("Selected Optimal Lag :",PLCH[4]                                                                  , "\n")
cat ("Information Criteria : Superme RT"                                                               , "\n")
cat ("R1 Test Statistics   :",tarusA$r1[tarusA$mhat],"/ R2 Test Statistics   :",tarusA$r2[tarusA$mhat] , "\n")
cat ("R1 5% Critical Value :",R1A                   ,"/ R2 5% Critical Value :",R2A                    , "\n")
cat ("++++++++++++++++++++++"                                                                          , "\n")
cat ("Caner & Hansen (2001) Threshold Effect Wald Test"                                                , "\n")
cat ("Test Statistics      :",pvalAus[1]                                                               , "\n")
cat ("Bootstrap p-value    :",pvalAus[2]                                                               , "\n")
cat ("\n")
cat ("Model B"                                                                                         , "\n")
cat ("Selected Optimal Lag :",PLCH[5]                                                                  , "\n")
cat ("Information Criteria : Superme RT"                                                               , "\n")
cat ("R1 Test Statistics   :",tarusB$r1[tarusB$mhat],"/ R2 Test Statistics   :",tarusB$r2[tarusB$mhat] , "\n")
cat ("R1 5% Critical Value :",R1B                   ,"/ R2 5% Critical Value :",R2B                    , "\n")
cat ("++++++++++++++++++++++"                                                                          , "\n")
cat ("Caner & Hansen (2001) Threshold Effect Wald Test"                                                , "\n")
cat ("Test Statistics      :",pvalBus[1]                                                               , "\n")
cat ("Bootstrap p-value    :",pvalBus[2]                                                               , "\n")
cat ("\n")
cat ("Model C"                                                                                         , "\n")
cat ("Selected Optimal Lag :",PLCH[6]                                                                  , "\n")
cat ("Information Criteria : Superme RT"                                                               , "\n")
cat ("R1 Test Statistics   :",tarusC$r1[tarusC$mhat],"/ R2 Test Statistics   :",tarusC$r2[tarusC$mhat] , "\n")
cat ("R1 5% Critical Value :",R1C                   ,"/ R2 5% Critical Value :",R2C                    , "\n")
cat ("++++++++++++++++++++++"                                                                          , "\n")
cat ("Caner & Hansen (2001) Threshold Effect Wald Test"                                                , "\n")
cat ("Test Statistics      :",pvalCus[1]                                                               , "\n")
cat ("Bootstrap p-value    :",pvalCus[2]                                                               , "\n")
cat ("\n")
}

printlog(tri,usi)
printadf(tri,usi,ptr,pus)
printlnv(tri,usi,PLNV)
printlch(tri,usi,PLCH)

# END
