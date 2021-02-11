#---Simulate Repeated Measures Designs with Missing Values-------#
library(mvtnorm)
library(MASS)
library(Matrix)
library(psych)
library(multcomp)
library(mice)


#----Necessary: Empriical Distribution function adjusted for missings-------#
Fihat=function(x,xii,lambdaakt,lambdaiakt){
#--count function---#

  Fihatk=0
  Fihatk0=which(lambdaakt==0)
  Fihatk1=which(lambdaakt==1)

  Fihatk[Fihatk0] = 0
  Fihatk[Fihatk1] = (x>xii[Fihatk1])+1/2*(x==xii[Fihatk1])
  
  1/lambdaiakt*sum(Fihatk)
}

# Domhof Procedure 

Domhof <- function(y, lambda){
  
  n <- dim(y)[1]
  d <- dim(y)[2]
  
  y_NA <- y
  
  for(j in 1:d){
    for(i in 1:n){
      if(lambda[i,j] == 0) y_NA[i,j] = NA
    }
  }  
  
  
  # Ranks
  R <- matrix(rank(y_NA, na.last = "keep"), ncol = d)
  N <- sum(lambda)
  
  
  # Relative effects
  p <- (R-0.5)/N
  p <- colMeans(p, na.rm = T)
  
  
  # Covariance matrix
  lambda_d <- colSums(lambda)
  
  
  # Covariance matrix formula
  V <- matrix(rep(0,d*d), ncol = d)
  for(i in 1:d){
    for(j in 1:d){
      if(i == j) V[i,j] <-  n/lambda_d[i]*var(R[,i], na.rm = T)/N^2
      #V[i,j] <- (lambda_d[i]-1)*var(R[,i], na.rm = T)*n/(N^2*lambda_d[i]*(lambda_d[i]-1))
      if(i != j){
        V[i,j] <- n/(N^2*(lambda_d[i]-1)*(lambda_d[j]-1) + n*sum(lambda[,i] == lambda[,j]&lambda[,i]==1)-1)*cov(R[,i], R[,j], use = "pairwise.complete.obs")*(sum(lambda[,i] == lambda[,j]&lambda[,i]==1)-1)
        # V[i,j] <- 1/(n*d*((lambda_d[i]-1)*(lambda_d[j]-1) + n*d*sum(lambda[,i] == lambda[,j]& lambda[,i] ==1)-1))*cov(R[,i], R[,j], use = "pairwise.complete.obs")*(sum(lambda[,i] == lambda[,j]& lambda[,i] ==1)-1)
        
      }
    }
  }
  #if(sum(is.na(V)) > 0){
  #  nsim <- nsim -1
  #  next
  #} 
  if(sum(is.na(V)) > 0){
    erg_WTS_dom <- NA
    erg_ATS_dom <- NA
  }else{
    C <- diag(1,d) - matrix(rep(1/d, d*d), ncol = d)
    
    # WTS
    WTS = n*t(p)%*%t(C)%*%ginv(C%*%V%*%t(C))%*%C%*%p
    critWTS <- qchisq(0.95, df =  rankMatrix(C))
    erg_WTS_dom <- (WTS > critWTS)
    
    # ATS
    M <- t(C)%*%ginv(C%*%t(C))%*%C
    ATS <-n * (tr(M%*%V))/(tr(M%*%V%*%M%*%V)) * t(p)%*%M%*%p
    
    df_chisq_ATS <- tr(M%*%V)^2/tr(M%*%V%*%M%*%V)
    crit_ATS <- qchisq(0.95, df = df_chisq_ATS)
    
    erg_ATS_dom <- (ATS > crit_ATS)
  }
  

  
  result_dom <- c(erg_WTS_dom, erg_ATS_dom)
  return(result_dom)
}

# Add alternative degrees of freedom calculation here


# Original Test Procedures
Original <- function(y, lambda){
  
  n <- dim(y)[1]
  d <- dim(y)[2]
  # Number of missing observations for each timepoint
  lambdai=colSums(lambda)
  
  # Helping matrixes/vectors
  aa=expand.grid(1:d,1:d)
  i1=aa[,2]
  j1=aa[,1]
  ihelp1=which(i1==j1)
  
  # Calculate all pairwise F_i(X_jk)
  pairwise=matrix(0,nrow=n,ncol=d*d)
  ncp=d*d
  for(i in 1:n){
    for(j in 1:ncp) {
      if(lambda[i,i1[j]]==0){pairwise[i,j] =0}
      if(lambda[i,i1[j]]==1){pairwise[i,j]=Fihat(y[i,i1[j]],y[,j1[j]],lambda[,j1[j]],lambdai[j1[j]]) }
    }
  }
  
  # Pairwise relative effects p_ij
  lambdaivec=lambdai[i1]
  pij = colSums(pairwise)/lambdaivec
  
  #--------------------------Compute now the Fi(Xik)------------------------------#
  
  FiXi=cbind(pairwise[,ihelp1])
  FiXiE = lambda*matrix(rep(1/2,d),nrow=n,ncol=d,byrow=TRUE) 
  #---------------------------Compute now G(Xik)----------------------------------#
  GXik = matrix(0,nrow=n,ncol=d)
  s=1:d
  for(i in 1:d){
    ihelp=which(i1==i)
    GXik[,i] = 1/d*(rowSums(pairwise[,ihelp]))
  } 
  
  # vector of relative effects
  phatvec = colSums(GXik)/lambdai
  
  # Expectation of G(Xik)
  GXikE = lambda*matrix(phatvec,nrow=n,ncol=d,byrow=TRUE)
  
  #----------------------Compute now all pairwise--------------------------------#
  
  # Helping matrices
  mathelp=matrix(0,nrow=n,ncol=d)
  mathelpE=matrix(0,nrow=n,ncol=d)
  
  # Help terms for last sum (s != i)                       
  for(j in 1:d){
    sakt=which(j1==j & i1!=j)
    mathelp[,j]=1/d*(rowSums(pairwise[,sakt]/matrix(rep(lambdai[i1[sakt]],n), nrow = n, byrow = T))) 
    mathelpE[,j] = (rowSums(matrix(pij[sakt]/lambdai[i1[sakt]],nrow=n,ncol=(d-1),byrow=TRUE)*lambda[,i1[sakt]]))
  }
  
  # Psi_ik and Expectation of Psi_ik
  Psik = n*(1/matrix(rep(lambdai,n), nrow = n, byrow = T)*(GXik-1/d*FiXi))-n*mathelp
  PsikE = n*(1/matrix(rep(lambdai,n), nrow = n, byrow = T)*(GXikE - 1/d*FiXiE))-1/d*n*mathelpE
  
  # Covariance matrix
  Psikvec = Psik - PsikE
  Vhat= t(Psikvec)%*%Psikvec/((n-1))
  
  # Contrast matrix
  C <- diag(d)-1/d
  nc <- nrow(C)
  
  Cphatvec=C%*%phatvec
  CVC = C%*%Vhat%*%t(C)
  
  
  if(sum(Vhat==0) > 0 | sum(is.na(CVC))>0 |isCorrelation(cov2cor(CVC)) == F) {
    erg_WTS <- NA
    erg_ATS <- NA
    erg_ATS2 <- NA
    erg_MCTP <- NA
  } else{
    #----------------------Testing--------------------------------#
    
    
    
    # Check wether dataset is degenerate
    #if(sum(lambdai==0) > 0 | sum(diag(CVC)<=0) > 0 |isCorrelation(cov2cor(C%*%Vhat%*%t(C))) == F ){
    #if(sum(diag(CVC)<=0) > 0 ){
    #  #nsim <- nsim -1
    #  break
    #} 
    
    
    # WTS 
    WTS = n*t(phatvec)%*%t(C)%*%ginv(C%*%Vhat%*%t(C))%*%C%*%phatvec
    critWTS <- qchisq(0.95, df =  rankMatrix(C))
    erg_WTS= (WTS > critWTS)
    
    # ATS
    trTV=sum(c(diag(CVC)))
    trTV2=trTV^2
    trTVTV=sum(c(diag(CVC%*%CVC)))
    dfF=trTV2/trTVTV
    ATS=n*t(Cphatvec)%*%Cphatvec/trTV*dfF
    crit_ATS=qchisq(0.95,dfF)
    erg_ATS=(ATS>crit_ATS)
    
    
    # MCTP 
    Test <- sqrt(n)*C%*%phatvec/sqrt(c(diag(C%*%Vhat%*%t(C))))
    T0 <- max(abs(Test))
    test1 = 1- pmvt(lower = -T0,upper = T0, delta=rep(0,nc), corr = cov2cor(C%*%Vhat%*%t(C)), df = n-1)[1]
    erg_MCTP = (0.05 > test1)
    
    
    
    # ATS with new degree of freedom estimation
    ATS2 <- n*t(Cphatvec)%*%Cphatvec/trTV
    crit_ATS2 <- qf(0.95, df1 = dfF, df2 = (n-1)*dfF)
    erg_ATS2 <- (ATS2 > crit_ATS2)
  }
  result <- c(erg_WTS, erg_ATS, erg_MCTP, erg_ATS2)
  return(result)
}






#-----------------------------Simulation Program----------------------------#
#mySimu<-function(n,%missing,rho,d,nsim)
mySimu <- function(n, r, dist, sigma, MM, nsim){

  # Covariance matrix
  if(sigma == "1") V0 <- matrix(c(1, 0, 0, 0, 1, 0, 0, 0, 1), ncol=3)
  if(sigma == "2") V0 <- matrix(c(3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3), ncol=4)
  if(sigma == "3") V0 <- matrix(c(1, 0, 0, 0, 3, 0, 0, 0, 6), ncol=3)
  if(sigma == "4") V0 <- matrix(c(1, 0.5, 0.7, 0.5, 5, 0.8, 0.7, 0.8, 9), ncol=3)
  if(sigma == "5") V0 <- matrix(c(1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 6, 0, 0, 0, 0, 12), ncol=4)
  if(sigma == "6") V0 <- matrix(c(1, 0.2, 0.4, 0.6, 0.2, 3, 0.7, 0.5, 0.4, 0.7, 6, 0.6, 0.6, 0.5, 0.6, 12), ncol=4)
  
  # Number of repeated measures
  d <- ncol(V0)
  

  # Result vectors
  erg_ATS <- c()
  erg_ATS2 <- c()
  erg_WTS <- c()
  erg_MCTP <- c()
  
  erg_WTS_med <- c()
  erg_ATS_med <- c()
  erg_MCTP_med <- c()
  
  erg_WTS_cca <- c()
  erg_ATS_cca <- c()
  erg_MCTP_cca <- c()
  
  erg_dom_WTS <- c()
  erg_dom_ATS <- c()
  erg_dom_MCTP <- c()


  
  for(isim in 1:nsim){
    #### CREATE DATA SET #####
    # Create data
    if(dist == "Normal") {
      y <- rmvnorm(n, mean = rep(0,d), sigma = V0)
    }
    if(dist == "LogNormal"){
      y <- exp(rmvnorm(n = n, sigma = V0))
    }
    
    
    ### Create missings under MCAR or MAR ###
    
    # First option to generate Missing At Random Using Variance
    if(MM == "SIG"){
      # Calculate Variances over all observations in "observed Groups" 
      sig1 <- var(as.vector(y[,1]))
      sig2 <- var(as.vector(y[,3]))
      # First Group 
      y[y[,1] < -sig1,2] <- y[y[,1] < -sig1,2]*rbinom(length(y[y[,1] < -sig1,2]),1, 0.9)
      y[y[,3] < -sig2,4]*rbinom(length(y[y[,3] < -sig2,4]),1, 0.9)
      # Second Group
      y[(-sig1 < y[,1] & y[,1] < sig1),2] <- y[(-sig1 < y[,1] & y[,1] < sig1),2] * rbinom(length(y[(-sig1 < y[,1] & y[,1] < sig1),2]), 1, 0.7)
      y[(-sig2 < y[,3] & y[,3] < sig2),4] <- y[(-sig2 < y[,3] & y[,3] < sig2),4] * rbinom(length(y[(-sig2 < y[,3] & y[,3] < sig2),4]), 1, 0.7)
      # Third Group
      y[y[,1] > sig1,2] <- y[y[,1] > sig1,2]*rbinom(length(y[y[,1] > sig1,2]),1, 0.9)
      y[y[,3] > sig2,4] <- y[y[,3] > sig2,4]*rbinom(length(y[y[,3] > sig2,4]),1, 0.9)
      
    }
    
    if(MM == "MED"){
      # Calculate Medians over all observations in "Observed Groups"
      med1 <- median(y[,1])
      med2 <- median(y[,3])
      
      # First Group 
      y[y[,1] < med1,2] <- y[y[,1] < med1,2] * rbinom(length(y[y[,1] < med1,2]), 1, 0.9)
      y[y[,3] < med2,4] <- y[y[,3] < med2,4] * rbinom(length(y[y[,3] < med2,4]), 1, 0.9)
      
      # Second Group
      y[y[,1] > med1,2] <- y[y[,1] > med1,2] * rbinom(length(y[y[,1] > med1,2]), 1, 0.7)
      y[y[,3] > med2,4] <- y[y[,3] > med2,4] * rbinom(length(y[y[,3] > med2,4]), 1, 0.7)
      
    }
    
    if(MM == "SIG" | MM == "MED"){
      # Create Missing Matrix
      lambda <- matrix(rep(1, n*d), ncol = d)
      for(i in 1:n){
        for(j in 1:d){
          if(y[i,j] == 0){
            lambda[i,j] <- 0
          } 
        }
      }
    }
    
    if(MM == "MCAR"){
      # Create missings
      lambda <- matrix(rbinom(n*d,1,1-r),nrow=n,ncol=d)
      
    }
    
    
    
    # Check whether data is degenerative
    lambdai <- colSums(lambda)
    if(sum(lambdai==0) > 0 | sum(lambdai == 1) > 0) next;
    
    
    # Round data
    y <- round(y)
    
    
    
    #### ALL AVAILABLE CASE ANALYSIS ####
    
    # Our procedure
    original <- Original(y,lambda)
    erg_WTS[isim] <- original[1]
    erg_ATS[isim] <- original[2]
    erg_MCTP[isim] <- original[3]
    erg_ATS2[isim] <- original[4]
    
    # Domhof procedure
    domhof <- Domhof(y,lambda)
    erg_dom_WTS[isim] <- domhof[1]
    erg_dom_ATS[isim] <- domhof[2]
    
    
    #### MEDIAN IMPUTATION ####
    y_NA <- y
    y_imp <- y
    for(j in 1:d){
      for(i in 1:n){
        if(lambda[i,j] == 0) y_NA[i,j] = NA
      }
    }  
    
    # Calculate Medians
    med_NA <- function(x){median(x, na.rm=T)}
    med <- apply(y_NA, 2, med_NA)
    
    # Impute with Medians
    for(j in 1:d){
      for(i in 1:n){
        if(is.na(y_NA[i,j]) == T) y_imp[i,j] = med[j]
      }
    }
    
    # Set all lambda to 1
    lambda_imp <- matrix(rep(1,n*d), ncol = d)
    
    median <- Original(y_imp, lambda_imp)
    erg_WTS_med[isim] <- median[1]
    erg_ATS_med[isim] <- median[2]
    erg_MCTP_med[isim] <- median[3]
    
    
    #### Complete Case Analysis ####
    y_cca <- y_NA[complete.cases(y_NA),]
    lambda_cca <- lambda[complete.cases(y_NA),]
    if(is.vector(lambda_cca) == FALSE & is.null(lambda_cca) == FALSE){
      lambda_cca_i <- dim(lambda_cca)[1]
      if(lambda_cca_i > d){
        cca <- Original(y_cca, lambda_cca)
        erg_WTS_cca[isim] <- cca[1]
        erg_ATS_cca[isim] <- cca[2]
        erg_MCTP_cca[isim] <- cca[3]
      }
    }
  }
  
  
  # Dataframe with results
  result <- data.frame(nsim = nsim, n = n, d = d, p_miss = r, Dist = dist, Sigma = sigma, MM = MM, WTS = mean(erg_WTS, na.rm = T),
                     ATS = mean(erg_ATS, na.rm = T), ATS2 = mean(erg_ATS2, na.rm = T), MCTP = mean(erg_MCTP, na.rm = T), WTSmed = mean(erg_WTS_med, na.rm = T),
                     ATSmed = mean(erg_ATS_med, na.rm = T), MCTPmed = mean(erg_MCTP_med, na.rm = T),
                     WTS_cca = mean(erg_WTS_cca, na.rm =T), ATS_cca = mean(erg_ATS_cca, na.rm = T), MCTP_cca = mean(erg_MCTP_cca, na.rm = T),
                     WTS_domhof = mean(erg_dom_WTS, na.rm =T), ATS_domhof = mean(erg_dom_ATS, na.rm = T))
  print(result)
  write.table(result, "revised_results.txt", row.names = F, col.names = F, quote = F, append = T)
}


Dist <- c("Normal", "LogNormal")
n <- c(10,20,30)
p_miss <- c(0,0.1,0.2,0.3)
sig <- c("1","2","3","4","5","6")

MissMech <- c("SIG", "MED")
sig4 <- c("2", "5", "6")




set.seed(1234)

### Simulation only for MCAR
for(h in 1:length(sig)){
  for(hh in 1:length(Dist)){
    for(hhh in 1:length(n)){
      for(hhhh in 1:length(p_miss)){
        mySimu(n = n[hhh], r = p_miss[hhhh], dist = Dist[hh], sigma = sig[h], MM = "MCAR", nsim = 10000)
      }
    }
  }
}

# Simulation for MAR (both versions)

for(h in 1:length(MissMech)){
  for(hh in 1:length(sig4)){
    for(hhh in 1:length(Dist)){
      for(hhhh in 1:length(n)){
        for(hhhhh in 1:length(p_miss))
        mySimu(n = n[hhhh], r = p_miss[hhhhh], dist = Dist[hhh], sigma = sig4[hh], MM = MissMech[h], nsim = 10000)
      }
    }
  }
}



mySimu(10,0.2,"Normal", "2", "MCAR", 1000)

