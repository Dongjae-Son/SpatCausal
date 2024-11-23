expit <- function(x){1/(1+exp(-x))}

logit <- function(x){log(x)-log(1-x)}

corfx <- function(u, phi, kappa, matern=TRUE){
  if(!matern) {kappa <- 0.5}
  corr <- matern(u, phi, kappa)
  corr[u==0] <- 1
  return(corr)
}

update.z <- function(oldz, y, mu, sig, MH=1){
  n <- length(oldz)
  canz <- rnorm(n,oldz,MH*sig)
  R <- dpois(y,exp(canz),log=TRUE) + dnorm(canz,mu,sig,log=TRUE) -
    dpois(y,exp(oldz),log=TRUE) - dnorm(oldz,mu,sig,log=TRUE) 
  out <- ifelse(log(runif(n))<R,canz,oldz)
  return(out)
}

HMC_naive = function (U, grad_U, epsilon = 0.01, L = 10, current_q)
{
  dist = numeric(L+1)
  
  q = current_q
  p = rnorm(length(q),0,1)  # independent standard normal variates
  current_p = p
  
  # Make a half step for momentum at the beginning
  
  p = p - epsilon * grad_U(q) / 2
  
  # Alternate full steps for position and momentum
  for (i in 1:L)
  {
    # Make a full step for the position
    q = q + epsilon * p
    dist[i+1] = sqrt (sum((q-current_q)^2))
    
    # Make a full step for the momentum, except at end of trajectory
    
    if (i!=L) p = p - epsilon * grad_U(q)
  }
  
  # Make a half step for momentum at the end.
  
  p = p - epsilon * grad_U(q) / 2
  
  # Negate momentum at end of trajectory to make the proposal symmetric
  
  p = -p
  
  # Evaluate potential & kinetic energies at start & end of trajectory
  
  current_U = U(current_q)
  current_K = sum(current_p^2) / 2
  proposed_U = U(q)
  proposed_K = sum(p^2) / 2
  
  # Accept or reject the state at end of trajectory, returning either
  # the position at the end of the trajectory or the initial position
  
  R <- current_U - proposed_U + current_K - proposed_K
  R <- ifelse(is.na(R), -Inf, R)
  
  if (log(runif(1)) < R) {
    return (list("accept", q)) # accept
  }
  else {
    return (list("reject", current_q)) # reject
  }
}

Mat.PO.share <-  function(Y, Tr, N0, N1, domain, X, Z, H, L = 20, tau = rep(1/L, 2),
                          center.X = TRUE, center.Z = TRUE, update.gamma = TRUE,
                          pri_sd_phi = 10, pri_sd_beta = 10, a = 0.1, b = 0.1, 
                          pri_sd_delta = 10, pref_samp = TRUE, fix_rho = FALSE,
                          iters = 20000, burn = 5000, thin = 1, verbose = FALSE, 
                          update = 2000, HMC = TRUE, euclidean = FALSE, ppp = rep(TRUE, nrow(Z)), 
                          rho_mn = 0, rho_sd = 1, fix_kappa.u = FALSE, fix_kappa.v = FALSE){
  
  # function that performs MCMC for hierarchical causal model with preferential sampling considered (setting beta0 = beta1 = beta and delta0 = delta1 = delta)
  # Inputs defined as:
  # Y: observed response (Y = Y1*Tr + Y0*(1-Tr))
  # Tr: binary policy (1: trt, 0: ctrl)
  # N0, N1: G times 1 vector where gth entry indicates the number of observation with policy a=0,1 at gth grid cell
  # X, Z: matrices for site-specific and grid-level covariates without intercept
  # H: n times G matrix. If gth entry of ith row is 1, this indicates that ith obs is in gth grid
  # L, tau: the number of leapfrogs and the step size when performing HMC
  # center.X, center.Z: Logical values whether X and Z are centered
  # update.gamma: Logical value whether the gamma.u and gamma.v are updated or not. If FALSE, the values are set to zero
  # pri_sd_beta, pri_sd_delta: prior sd for beta and delta
  # a, b: Inverse gamma prior parameters
  # pref_samp: Logical value. If TRUE, this function considers pref. sampling
  # fix_rho: Logical value. If TRUE, conducts Metropolis sampler on dependence hyperparameter of CAR priors
  # iters, burn: the total number of MCMC iterations including the number of burn-in samples
  # thin: thinning
  # verbose, update: Logical value. If TRUE, this function returns updates of iterations
  # HMC: Logical value. If TRUE, this function performs HMC to update log of lambda0 and log of lambda1
  # euclidean: Logical value. If FALSE, the distance between each pair of the grid cells is calculated based on rdist.earth function in fields package
  # ppp: A logical vector of length equal to the number of grid cells, to subset the domain
  # rho_mn, rho_sd: Mean and standard deviations of the prior for log(rho.u) and log(rho.v)
  # fix_kappa.u, fix_kappa.v: Logical values. If TRUE, set kappa.u = kappa.v = 0.5
  
  
  library(spam)
  library(geoR)
  
  tick <- proc.time()[3]
  
  iters_thin <- (iters-burn)*thin
  X_center <- as.matrix(X)
  Z_center <- as.matrix(Z)
  
  if(center.X) {X_center <- scale(X_center, center = TRUE, scale = FALSE)}
  if(center.Z) {Z_center <- scale(Z_center, center = TRUE, scale = FALSE)}
  
  Z_center <- Z_center[ppp,]
  cov.names <- colnames(Z)
  
  domain <- domain[ppp,]
  H <- H[,ppp]
  
  # Bookkeeping
  
  N0 <- N0[ppp]
  N1 <- N1[ppp]
  N <- N0 + N1
  
  Y0 <- Y1 <- rep(NA, nrow(X))
  Y0[which(Tr == 0)] <- Y[which(Tr == 0)]
  Y1[which(Tr == 1)] <- Y[which(Tr == 1)]
  
  na.y0 <- which(is.na(Y0))
  na.y1 <- which(is.na(Y1))
  
  G <- sum(as.numeric(ppp))  
  p <- ncol(X)
  q <- ncol(Z)
  
  # distance matrix
  if(euclidean) {
    distMat <- as.matrix(dist(domain))
  } else {
    distMat <- fields::rdist.earth(domain, domain, miles = FALSE)
  }
  diag(distMat) <- 0
  
  # Initial values
  
  lin.mod <- lm(Y~Tr+X_center)
  glm.mod <- summary(glm(N1~Z_center, family="poisson"))
  
  eta0 <- eta1 <- as.vector(glm.mod$coefficients[,1])[1]
  delta <- as.vector(glm.mod$coefficients[,1])[-1]
  
  alpha0 <- as.vector(lin.mod$coefficients)[1]
  alpha1 <- sum(as.vector(lin.mod$coefficients)[c(1,2)])
  
  beta <- as.vector(lin.mod$coefficients)[-c(1,2)]
  
  sig2y0 <- sum(lin.mod$residuals^2)/sum(N)
  sig2y1 <- sig2y0
  
  rho.u <- rho.v <- exp(rho_mn)
  kappa.u <- kappa.v <- 0.5
  
  # Matern covariance
  CorU <- corfx(distMat, rho.u, kappa.u)
  CorV <- corfx(distMat, rho.v, kappa.v)
  
  InvCorU <- solve(CorU)
  InvCorV <- solve(CorV)
  
  sig2u0 <- sig2u1 <- sig2v0 <- sig2v1 <- 1
  u0t <- u1t <- v0t <- v1t <- rep(0, G)
  
  gamma.u <- gamma.v <- 0.5
  phi0 <- phi1 <- 0.0
  
  u0 <- u0t
  u1 <- u1t + gamma.u * u0t
  
  v0 <- v0t
  v1 <- v1t + gamma.v * v0t
  
  L0 <- as.vector(colSums(t(Z_center)*delta) + eta0 + v0 + phi0*u0)
  L1 <- as.vector(colSums(t(Z_center)*delta) + eta1 + v1 + phi1*u1)
  
  psi0 <- psi1 <- 0.1
  
  
  # Keep track of stuff
  
  keepers <- matrix(NA, iters, p + q + 18 + 2)
  colnames(keepers) <- c("eta0", "eta1", paste("delta", cov.names),
                         "alpha0", "alpha1", paste("beta", cov.names),
                         "rho.u", "rho.v", "phi0", "phi1", "gamma.u", "gamma.v", 
                         "sig2u0", "sig2u1", "sig2v0", "sig2v1", "kappa.u", "kappa.v",
                         "psi0", "psi1", "sig2y0", "sig2y1")
  
  ATE_vec <- rep(NA, iters)
  ATE_obs_vec <- rep(NA, iters)
  ATE_ppp_vec <- rep(NA, iters)
  ATE_sample_vec <- rep(NA, iters)
  
  prop.score <- prop.score.obs <- posit.vec <- 0
  local_effect <- local_var <- 0
  
  u0_mn <- u1_mn <- v0_mn <- v1_mn <- 0
  u0_var <- u1_var <- v0_var <- v1_var <- 0
  
  
  # MCMC setup
  
  ## Intensities
  
  acc.HMC <- rep(0, 2)
  names(acc.HMC) <- c("L0", "L1")
  att.HMC <- acc.HMC
  
  ## rho
  
  acc.rho <- rep(0, 2)
  names(acc.rho) <- c("rho.u", "rho.v")
  att.rho <- acc.rho
  MH.rho <- rep(0.1, 2)
  
  ## kappa
  
  acc.kappa <- rep(0, 2)
  names(acc.kappa) <- c("kappa.u", "kappa.v")
  att.kappa <- acc.kappa
  MH.kappa <- rep(0.1, 2)
  
  
  for(iter in 1:(burn+iters_thin)){
    ############################################
    ## Bayesian imputation for missing values ##
    ############################################
    
    u0.vec <- as.vector(H%*%u0)
    u1.vec <- as.vector(H%*%u1)
    
    Y0[na.y0] <- rnorm(sum(N1), (X_center%*%beta + u0.vec)[na.y0], sqrt(sig2y0)) + alpha0
    Y1[na.y1] <- rnorm(sum(N0), (X_center%*%beta + u1.vec)[na.y1], sqrt(sig2y1)) + alpha1
    
    
    #########################################
    ## Parameters involving normal layer Y ##
    #########################################
    
    
    # alpha0 
    u0.vec <- as.vector(H%*%u0)
    Cov.y <- 1/(nrow(X_center)/sig2y0 + 1/pri_sd_beta^2)
    mean.y <- sum(Y0-u0.vec-X_center%*%beta)/sig2y0
    alpha0 <- rnorm(1, Cov.y*mean.y, sqrt(Cov.y))
    
    # alpha1 
    u1.vec <- as.vector(H%*%u1)
    Cov.y <- 1/(nrow(X_center)/sig2y1 + 1/pri_sd_beta^2)
    mean.y <- sum(Y1-u1.vec-X_center%*%beta)/sig2y1
    alpha1 <- rnorm(1, Cov.y*mean.y, sqrt(Cov.y))
    
    # beta
    Qbeta <- t(X_center)%*%X_center/sig2y0 + t(X_center)%*%X_center/sig2y1 + diag(p)/pri_sd_beta^2
    bbeta <- t(X_center)%*%((Y0-alpha0-u0.vec)/sig2y0 + (Y1-alpha1-u1.vec)/sig2y1)
    beta <- as.vector(rmvnorm(1, solve(Qbeta)%*%bbeta, solve(Qbeta)))
    
    # sig2y0
    QF.y <- sum((Y0-X_center%*%beta-alpha0-u0.vec)^2)
    sig2y0 <- 1/rgamma(1, sum(N)/2+a, QF.y/2+b)
    
    # sig2y1
    QF.y <- sum((Y1-X_center%*%beta-alpha1-u1.vec)^2)
    sig2y1 <- 1/rgamma(1, sum(N)/2+a, QF.y/2+b)
    
    
    #############################################
    ## Latent spatial random effects U0 and U1 ##
    #############################################
    
    Xb0 <- as.vector(X_center%*%beta) + alpha0
    Xb1 <- as.vector(X_center%*%beta) + alpha1
    
    # u0.tilde
    u1t.vec <- as.vector(H%*%u1t)
    mu0u <- as.vector(t(H)%*%(Y0-Xb0))/sig2y0
    mu1u <- as.vector(t(H)%*%(Y1-Xb1-u1t.vec))*gamma.u/sig2y1
    
    Q0u <- diag(N/sig2y0)
    Q1u <- diag(N*gamma.u^2/sig2y1)
    
    if(pref_samp){
      Zb0 <- as.vector(Z_center%*%delta) + eta0
      Zb1 <- as.vector(Z_center%*%delta) + eta1
      
      mu0v <- (L0-Zb0-v0)*phi0/psi0
      mu1v <- (L1-Zb1-v1-phi1*u1t)*(phi1*gamma.u)/psi1
      
      Q0v <- diag(G)*phi0^2/psi0 
      Q1v <- diag(G)*(phi1*gamma.u)^2/psi1 
      
      Q <- Q0u + Q1u + Q0v + Q1v + InvCorU/sig2u0
      bb <- mu0u + mu1u + mu0v + mu1v
      u0t <- as.vector(rmvnorm.canonical(1, bb, Q))
    } else {
      Q <- Q0u + Q1u + InvCorU/sig2u0
      bb <- mu0u + mu1u
      u0t <- as.vector(rmvnorm.canonical(1, bb, Q)) 
    }
    
    
    # u1.tilde
    u0t.vec <- as.vector(H%*%u0t)
    mu1u <- as.vector(t(H)%*%(Y1-Xb1-gamma.u*u0t.vec))/sig2y1
    Q1u <- diag(N/sig2y1)
    
    if(pref_samp){
      mu1v <- (L1-Zb1-v1-(phi1*gamma.u)*u0t)*phi1/psi1
      Q1v <- diag(G)*phi1^2/psi1
      
      Q <- Q1u + Q1v + InvCorU/sig2u1
      bb <- mu1u + mu1v
      u1t <- as.vector(rmvnorm.canonical(1, bb, Q))
    } else {
      Q <- Q1u + InvCorU/sig2u1
      bb <- mu1u
      u1t <- as.vector(rmvnorm.canonical(1, bb, Q))
    }
    
    
    ####################################
    ## Linear model of coreg. gamma u ##
    ####################################
    
    u0t.vec <- as.vector(H%*%u0t)
    u1t.vec <- as.vector(H%*%u1t)
    mu1u <- as.vector(t(H)%*%(Y1-Xb1-u1t.vec))
    
    if(pref_samp){
      mu1v <- (L1-Zb1-v1-phi1*u1t)
      var.pt <- sum(u0t.vec^2)/sig2y1 + sum(u0t^2)*phi1^2/psi1 + 1/pri_sd_beta^2 
      mean.pt <- sum(u0t.vec*(Y1-Xb1-u1t.vec))/sig2y1 + sum(mu1v*u0t)*phi1/psi1 
      gamma.u <- rnorm(1, mean.pt/var.pt, sqrt(1/var.pt))
    } else {
      var.pt <- sum(u0t.vec^2)/sig2y1 + 1/pri_sd_beta^2
      mean.pt <- sum(u0t.vec*(Y1-Xb1-u1t.vec))/sig2y1
      gamma.u <- rnorm(1, mean.pt/var.pt, sqrt(1/var.pt))
    }
    
    u0 <- u0t
    u1 <- u1t + gamma.u*u0t
    
    
    #######################################
    ## Variance parameters for U0 and U1 ##
    #######################################
    
    QF.u <- as.numeric(t(u0t)%*%InvCorU%*%u0t)
    sig2u0 <- 1/rgamma(1, G/2 + a, QF.u/2 + b)
    
    QF.u <- as.numeric(t(u1t)%*%InvCorU%*%u1t)
    sig2u1 <- 1/rgamma(1, G/2 + a, QF.u/2 + b)
    
    
    ###############################################################################
    ## Dependence and smoothness parameter of latent spatial processes U0 and U1 ##
    ###############################################################################
    
    # rho.u
    if(isFALSE(fix_rho)){
      att.rho[1] <- att.rho[1] + 1
      curlp <- 
        2*sum(log(diag(t(chol(InvCorU)))))-
        t(u0t)%*%InvCorU%*%u0t/(2*sig2u0)-
        t(u1t)%*%InvCorU%*%u1t/(2*sig2u1)+
        dnorm(log(rho.u), rho_mn, rho_sd, TRUE)
      
      can.rho.u <- exp(rnorm(1, log(rho.u), MH.rho[1]))
      canCorU <- corfx(distMat, can.rho.u, kappa.u)
      InvcanCorU <- solve(canCorU)
      
      canlp <- 
        2*sum(log(diag(t(chol(InvcanCorU)))))-
        t(u0t)%*%InvcanCorU%*%u0t/(2*sig2u0)-
        t(u1t)%*%InvcanCorU%*%u1t/(2*sig2u1)+
        dnorm(log(can.rho.u), rho_mn, rho_sd, TRUE)
      
      if(log(runif(1)) < as.numeric(canlp-curlp)){
        rho.u <- can.rho.u
        CorU <- canCorU
        InvCorU <- solve(CorU)
        acc.rho[1] <- acc.rho[1] + 1
      }
    }
    
    
    # kappa.u
    if(!fix_kappa.u){
      att.kappa[1] <- att.kappa[1] + 1
      curlp <- 
        2*sum(log(diag(t(chol(InvCorU)))))-
        t(u0t)%*%InvCorU%*%u0t/(2*sig2u0)-
        t(u1t)%*%InvCorU%*%u1t/(2*sig2u1)+
        dnorm(log(kappa.u), log(0.5), 1, TRUE)
      
      can.kappa.u <- exp(rnorm(1, log(kappa.u), MH.kappa[1]))
      canCorU <- corfx(distMat, rho.u, can.kappa.u)
      InvcanCorU <- solve(canCorU)
      
      canlp <- 
        2*sum(log(diag(t(chol(InvcanCorU)))))-
        t(u0t)%*%InvcanCorU%*%u0t/(2*sig2u0)-
        t(u1t)%*%InvcanCorU%*%u1t/(2*sig2u1)+
        dnorm(log(can.kappa.u), log(0.5), 1, TRUE)
      
      if(log(runif(1)) < as.numeric(canlp-curlp)){
        kappa.u <- can.kappa.u
        CorU <- canCorU
        InvCorU <- solve(CorU)
        acc.kappa[1] <- acc.kappa[1] + 1
      }
    }
    
    
    if(pref_samp){
      #######################
      # The intensity parts #
      #######################
      
      Zb0 <- as.vector(Z_center%*%delta) + eta0
      Zb1 <- as.vector(Z_center%*%delta) + eta1
      
      # L0
      if(HMC){
        logU <- function(q){
          sum((q - (Zb0+v0+phi0*u0))^2)/(2*psi0) - sum(dpois(N0, exp(q), TRUE))
        }
        
        gradU <- function(q){
          (q - (Zb0+v0+phi0*u0))/psi0 - (N0 - exp(q))
        }
        
        att.HMC[1] <- att.HMC[1] + 1
        new_L0 <- HMC_naive(logU, gradU, tau[1], L, L0)
        if(new_L0[[1]] == "accept") {
          acc.HMC[1] <- acc.HMC[1] + 1
          L0 <- new_L0[[2]]
        }
      } else {
        L0 <- update.z(L0, N0, (Zb0+v0+phi0*u0), sqrt(psi0))
      }
      
      
      # L1
      if(HMC){
        logU <- function(q){
          sum((q - (Zb1+v1+phi1*u1))^2)/(2*psi1) - sum(dpois(N1, exp(q), TRUE))
        }
        
        gradU <- function(q){
          (q - (Zb1+v1+phi1*u1))/psi1 - (N1 - exp(q))
        }
        
        att.HMC[2] <- att.HMC[2] + 1
        new_L1 <- HMC_naive(logU, gradU, tau[2], L, L1)
        if(new_L1[[1]] == "accept") {
          acc.HMC[2] <- acc.HMC[2] + 1
          L1 <- new_L1[[2]]
        }
      } else {
        L1 <- update.z(L1, N1, (Zb1+v1+phi1*u1), sqrt(psi1))
      }
      
      
      # v0.tilde
      mu0v <- (L0-Zb0-phi0*u0)/psi0
      mu1v <- (L1-Zb1-v1t-phi1*u1)*gamma.v/psi1
      
      Q0v <- diag(G)/psi0 # ppp
      Q1v <- diag(G)*gamma.v^2/psi1 # ppp
      
      Q <- Q0v + Q1v + InvCorV/sig2v0
      bb <- mu0v + mu1v
      v0t <- as.vector(rmvnorm.canonical(1, bb, Q))
      
      
      # v1.tilde
      mu1v <- (L1-Zb1-gamma.v*v0t-phi1*u1)/psi1
      Q1v <- diag(G)/psi1 
      Q <- Q1v + InvCorV/sig2v1
      bb <- mu1v
      v1t <- as.vector(rmvnorm.canonical(1, bb, Q))
      
      
      # gamma.v
      bgamma.v <- sum(v0t*(L1-Zb1-v1t-phi1*u1))/psi1 
      Cgamma.v <- sum(v0t^2)/psi1 + 1/pri_sd_delta^2 
      gamma.v <- rnorm(1, bgamma.v/Cgamma.v, sqrt(1/Cgamma.v))
      
      v0 <- v0t
      v1 <- v1t + gamma.v*v0t
      
      
      # eta0, phi0
      Zu <- cbind(rep(1, G), u0) 
      b.eta0 <- t(Zu)%*%(L0-Z_center%*%delta-v0)/psi0
      Q.eta0 <- t(Zu)%*%Zu/psi0 + diag(ncol(Zu))/pri_sd_delta^2
      etaphi0 <- rmvnorm(1, solve(Q.eta0)%*%b.eta0, solve(Q.eta0))
      eta0 <- etaphi0[1]
      phi0 <- etaphi0[2]
      
      
      # eta1, phi1
      Zu <- cbind(rep(1, G), u1)
      b.eta1 <- t(Zu)%*%(L1-Z_center%*%delta-v1)/psi1
      Q.eta1 <- t(Zu)%*%Zu/psi1 + diag(ncol(Zu))/pri_sd_delta^2
      etaphi1 <- rmvnorm(1, solve(Q.eta1)%*%b.eta1, solve(Q.eta1))
      eta1 <- etaphi1[1]
      phi1 <- etaphi1[2]
      
      
      # delta
      bdelta <- t(Z_center)%*%(L0-eta0-v0-phi0*u0)/psi0 + t(Z_center)%*%(L1-eta1-v1-phi1*u1)/psi1 
      Qdelta <- t(Z_center)%*%Z_center*(1/psi0 + 1/psi1) + diag(q)/pri_sd_delta^2 
      delta <- as.vector(rmvnorm.canonical(1, bdelta, Qdelta))
      
      Zb0 <- as.vector(Z_center%*%delta) + eta0
      Zb1 <- as.vector(Z_center%*%delta) + eta1
      
      lambda0 <- exp(Zb0 + v0 + phi0*u0)
      lambda1 <- exp(Zb1 + v1 + phi1*u1)
      
      
      #######################################
      ## Variance parameters for L0 and L1 ##
      #######################################
      
      # psi0
      QF.L0 <- sum((L0-Zb0-v0-phi0*u0)^2) 
      psi0 <- 1/rgamma(1, G/2+a, QF.L0/2+b)
      
      
      # psi1
      QF.L1 <- sum((L1-Zb1-v1-phi1*u1)^2) 
      psi1 <- 1/rgamma(1, G/2+a, QF.L1/2+b)
      
      
      #######################################
      ## Variance parameters for V0 and V1 ##
      #######################################
      
      # sig2v0
      QF.v <- as.numeric(t(v0t)%*%InvCorV%*%v0t)
      sig2v0 <- 1/rgamma(1, G/2 + a, QF.v/2 + b)
      
      
      # sig2v1
      QF.v <- as.numeric(t(v1t)%*%InvCorV%*%v1t)
      sig2v1 <- 1/rgamma(1, G/2 + a, QF.v/2 + b)
      
      
      #################################################################
      ## Correlation parameter of latent spatial processes V0 and V1 ##
      #################################################################
      
      # rho.v
      if(isFALSE(fix_rho)){
        att.rho[2] <- att.rho[2] + 1
        curlp <- 
          2*sum(log(diag(t(chol(InvCorV)))))-
          t(v0t)%*%InvCorV%*%v0t/(2*sig2v0)-
          t(v1t)%*%InvCorV%*%v1t/(2*sig2v1)+
          dnorm(log(rho.v), rho_mn, rho_sd, TRUE)
        
        can.rho.v <- exp(rnorm(1, log(rho.v), MH.rho[2]))
        canCorV <- corfx(distMat, can.rho.v, kappa.v)
        InvcanCorV <- solve(canCorV)
        
        canlp <- 
          2*sum(log(diag(t(chol(InvcanCorV)))))-
          t(v0t)%*%InvcanCorV%*%v0t/(2*sig2v0)-
          t(v1t)%*%InvcanCorV%*%v1t/(2*sig2v1)+
          dnorm(log(can.rho.v), rho_mn, rho_sd, TRUE)
        
        if(log(runif(1)) < as.numeric(canlp-curlp)){
          rho.v <- can.rho.v
          CorV <- canCorV
          InvCorV <- solve(CorV)
          acc.rho[2] <- acc.rho[2] + 1
        }
      }
      
      
      # kappa.v
      if(!fix_kappa.v){
        att.kappa[2] <- att.kappa[2] + 1
        curlp <- 
          2*sum(log(diag(t(chol(InvCorV)))))-
          t(v0t)%*%InvCorV%*%v0t/(2*sig2v0)-
          t(v1t)%*%InvCorV%*%v1t/(2*sig2v1)+
          dnorm(log(kappa.v), log(0.5), 1, TRUE)
        
        can.kappa.v <- exp(rnorm(1, log(kappa.v), MH.kappa[2]))
        canCorV <- corfx(distMat, rho.v, can.kappa.v)
        InvcanCorV <- solve(canCorV)
        
        canlp <- 
          2*sum(log(diag(t(chol(InvcanCorV)))))-
          t(v0t)%*%InvcanCorV%*%v0t/(2*sig2v0)-
          t(v1t)%*%InvcanCorV%*%v1t/(2*sig2v1)+
          dnorm(log(can.kappa.v), log(0.5), 1, TRUE)
        
        if(log(runif(1)) < as.numeric(canlp-curlp)){
          kappa.v <- can.kappa.v
          CorV <- canCorV
          InvCorV <- solve(CorV)
          acc.kappa[2] <- acc.kappa[2] + 1
        }
      }
    }
    
    if(!pref_samp){
      phi0 <- phi1 <- 0
    }
    
    
    
    ##################################
    ## Tuning MCMC hyper-parameters ##
    ##################################
    
    # Step size tuning
    if(iter<burn){for(k in 1:length(tau)){if(att.HMC[k] > 50){
      if(acc.HMC[k]/att.HMC[k] < 0.7){tau[k] <- tau[k]*0.8}
      if(acc.HMC[k]/att.HMC[k] > 0.9){tau[k] <- tau[k]*1.2}
      acc.HMC[k] <- att.HMC[k] <- 0
    }}}
    
    if(iter<burn){for(k in 1:length(MH.rho)){if(att.rho[k] > 50){
      if(acc.rho[k]/att.rho[k] < 0.3){MH.rho[k] <- MH.rho[k]*0.8}
      if(acc.rho[k]/att.rho[k] > 0.5){MH.rho[k] <- MH.rho[k]*1.2}
      acc.rho[k] <- att.rho[k] <- 0
    }}}
    
    if(iter<burn){for(k in 1:length(MH.kappa)){if(att.kappa[k] > 50){
      if(acc.kappa[k]/att.kappa[k] < 0.3){MH.kappa[k] <- MH.kappa[k]*0.8}
      if(acc.kappa[k]/att.kappa[k] > 0.5){MH.kappa[k] <- MH.kappa[k]*1.2}
      acc.kappa[k] <- att.kappa[k] <- 0
    }}}
    
    # KEEP TRACK OF STUFF
    
    if(iter<burn) {
      keepers[iter,] <- c(eta0, eta1, delta, alpha0, alpha1, beta,
                          rho.u, rho.v, phi0, phi1, gamma.u, gamma.v, 
                          sig2u0, sig2u1, sig2v0, sig2v1, kappa.u, kappa.v,
                          psi0, psi1, sig2y0, sig2y1)
      
      ATE_vec[iter] <- alpha1 - alpha0 + mean(u1 - u0)
      
    } else {
      if(iter%%thin == 0) {
        keepers[burn+(iter-burn)/thin,] <- c(eta0, eta1, delta, alpha0, alpha1, beta,
                                             rho.u, rho.v, phi0, phi1, gamma.u, gamma.v, 
                                             sig2u0, sig2u1, sig2v0, sig2v1, kappa.u, kappa.v,
                                             psi0, psi1, sig2y0, sig2y1)
        
        ATE_vec[burn+(iter-burn)/thin] <- alpha1 - alpha0 + mean(u1 - u0)
        
        u0_mn <- u0_mn + u0/(iters-burn)
        u1_mn <- u1_mn + u1/(iters-burn)
        v0_mn <- v0_mn + v0/(iters-burn)
        v1_mn <- v1_mn + v1/(iters-burn)
        
        u0_var <- u0_var + u0^2/(iters-burn)
        u1_var <- u1_var + u1^2/(iters-burn)
        v0_var <- v0_var + v0^2/(iters-burn)
        v1_var <- v1_var + v1^2/(iters-burn)
        
        local_effect <- local_effect + (alpha1-alpha0 + u1-u0)/(iters-burn)
        local_var <- local_var + (alpha1-alpha0 + u1-u0)^2/(iters-burn)
        
        posit.vec <- posit.vec + as.numeric((alpha1 - alpha0 + u1 - u0)>0)/(iters-burn)
        if(pref_samp){
          prop.score <- prop.score + ((lambda1)/(lambda0 + lambda1))/(iters-burn)
          prop.score.obs <- prop.score.obs + ((lambda1)/(lambda0 + lambda1))[N!=0]/(iters-burn)
        }
      }
    }
    
    if(isTRUE(verbose)) {
      if(iter%%update == 0){
        cat(iter, "out of", burn+iters_thin, "number of iterations\n")
      }
    }
  }
  
  tock   <- proc.time()[3]
  output <- list(samps = keepers,
                 ATE = ATE_vec,
                 prop.score = prop.score,
                 posit.prob = posit.vec,
                 local_effect = local_effect,
                 local_var = local_var - local_effect^2,
                 uv_mn = cbind(u0_mn, u1_mn, v0_mn, v1_mn),
                 uv_var = cbind(u0_var-u0_mn^2, u1_var-u1_mn^2, 
                                v0_var-v0_mn^2, v1_var-v1_mn^2),
                 acc_HMC = acc.HMC/att.HMC,
                 acc_rate_rho = acc.rho/att.rho,
                 acc_rate_kappa = acc.kappa/att.kappa,
                 time = (tock-tick)/60) # time is minute scale
  
  return(output)
}