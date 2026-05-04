# ***************************************************
# *                                                 *
# *        Proposed Method Implementation           *
# *                                                 *
# ***************************************************


# Sigmoid function
expit <- function(x){1/(1+exp(-x))} 

# ------------------------------------------------------------------------------

# Logit function
logit <- function(x){log(x)-log(1-x)} 

# ------------------------------------------------------------------------------

# Matern Correlation function
# Arguments:
#   @u      A numeric vector of distances
#   @phi    Spatial dependence parameter
#   @kappa  Spatial smoothness parameter
#   @maturn Logical. If false, this function returns an exponential correlation
corfx <- function(u, phi, kappa, matern=TRUE){
  if(!matern) {kappa <- 0.5}
  corr <- matern(u, phi, kappa)
  corr[u==0] <- 1
  return(corr)
}

# ------------------------------------------------------------------------------

# Metropolis-Hastings update for latent log-intensities in a Poisson log-normal model
# Arguments:
#   @oldz Current latent log-intensity values (length n vector)
#   @y    Observed count data, assumed y | z ~ Poisson(exp(z))
#   @mu   Prior mean of the Gaussian prior on z
#   @sig  Prior SD of the Gaussian prior on z; also used as proposal scale
#   @MH   Tuning multiplier for the random-walk proposal SD. Default: 1
update.z <- function(oldz, y, mu, sig, MH=1){
  n <- length(oldz)
  canz <- rnorm(n,oldz,MH*sig)
  R <- dpois(y,exp(canz),log=TRUE) + dnorm(canz,mu,sig,log=TRUE) -
       dpois(y,exp(oldz),log=TRUE) - dnorm(oldz,mu,sig,log=TRUE) 
  out <- ifelse(log(runif(n))<R,canz,oldz)
  return(out)
}

# ------------------------------------------------------------------------------

# Hamiltonian Monte Carlo (HMC) update without preconditioning (From Neal (2011), "MCMC using Hamiltonian dynamics")
# Arguments:
#   @U           Negative log posterior as a function of the parameter of interest
#   @grad_U      Gradient of the negative log posterior
#   @epsilon     Leapfrog step size
#   @L           The number of leapfrog steps
#   @current_q   Current value of the parameter of interest
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

# ------------------------------------------------------------------------------

# Run Shared Model using the model from Pati et. al (2011)
# Arguments:
#   @Y             Observed outcome vector
#   @Tr            Treatment status vector
#   @N             The number of locations in each cell of the discretized domain
#   @domain        G by 2 matrix containing the centroids of the grid cells
#   @X             N by p covariate matrix for observations
#   @Z             G by p covariate matrix for grid cells 
#   @H             N by G matrix with (i,g) entry 1 if ith location belongs to gth cell (i = 1,...,N and g = 1,...,G)
#   @Leap          The number of leap frog steps
#   @tau_L         Leapfrog step size
#   @pri_sd_phi    Prior sd for phi (preferential sampling parameter)
#   @pri_sd_beta   Prior sd for beta (regression coefficients of the outcome)
#   @a             Shape paramter of inverse gamma priors
#   @b             Scale paramter of inverse gamma priors
#   @pri_sd_delta  Prior sd for delta (regression coefficients of the point process)
#   @fix_rho       Logical whether to update or fix rho, spatial dependence
#   @euclidean     Logical whether to use euclidean distances or pairwise great circle distances
#   @iters         The number of MCMC samples after burn-in
#   @burn          The number of burn-in samples
#   @update        Print progress every this many iterations. Ignored if verbose = FALSE
#   @thin          Keep every jth sample to reduce autocorrelation. Default: 1
#   @verbose       Logical whether to print progress messages
#   @fix_kappa.u   Logical whether to update or fix the spatial smoothness of U process
#   @fix_kappa.v   Logical whether to update or fix the spatial smoothness of V process
#   @rho_seq       The sequence of candidate rhos for discretized Metropolis sampler
#   @kappa_mn      Prior mean of the spatial smoothness parameters
#   @kappa_sd      Prior sd of the spatial smoothness parameters
Pati <- function(Y, Tr, N, domain, X, Z, H, Leap = 20, tau_L = 1/Leap,
                 pri_sd_phi = 10, pri_sd_beta = 10, a = 0.1, b = 0.1, 
                 pri_sd_delta = 10, fix_rho = FALSE, euclidean = TRUE, 
                 iters = 20000, burn = 5000, update = 2000, thin = 1,
                 verbose = FALSE, fix_kappa.u = TRUE, fix_kappa.v = TRUE,
                 rho_seq = seq(0.01, 0.2, by = 0.01), kappa_mn = log(0.5), kappa_sd = 1){
  
  library(Matrix)
  library(MASS)
  library(spam)
  library(geoR)
  
  tick <- proc.time()[3]
  iters_thin <- (iters-burn)*thin
  cov.names <- colnames(Z)
  
  # Bookkeeping
  G <- nrow(domain)
  p <- ncol(X)
  q <- ncol(Z)
  n <- nrow(X)
  
  # distance matrix
  if(euclidean) {
    distMat <- as.matrix(dist(domain))
  } else {
    distMat <- fields::rdist.earth(domain, domain, miles = FALSE)
  }
  diag(distMat) <- 0
  
  # covariates
  XA <- sweep(x = X, MARGIN = 1, STATS = Tr, FUN = "*")
  X_tot <- cbind(rep(1,n), Tr, X, XA)
  
  # Initial values
  
  lin.mod <- lm(Y~X_tot-1)
  glm.mod <- summary(glm(N~Z, family="poisson"))
  
  eta <- as.vector(glm.mod$coefficients[,1])[1]
  delta <- as.vector(glm.mod$coefficients[,1])[-1]
  
  alpha0 <- as.vector(lin.mod$coefficients)[1]
  alpha1 <- as.vector(lin.mod$coefficients)[2]
  beta0 <- as.vector(lin.mod$coefficients)[3:(p+2)]
  beta1 <- as.vector(lin.mod$coefficients)[(p+3):(2*p+2)]
  
  reg_coef <- c(alpha0, alpha1, beta0, beta1)
  sig2y <- sum(lin.mod$residuals^2)/sum(N)
  
  # Precomputes Matern covariance with rho and kappa grids 
  nr <- length(rho_seq)
  kappa.u <- kappa.v <- 0.5
  CorU.grid <- array(0, c(G, G, nr))
  CorV.grid <- array(0, c(G, G, nr))
  InvCorU.grid <- array(0, c(G, G, nr))
  InvCorV.grid <- array(0, c(G, G, nr))
  
  for(r in 1:nr){
    CorU.grid[,,r] <- corfx(distMat, rho_seq[r], kappa.u)
    CorV.grid[,,r] <- corfx(distMat, rho_seq[r], kappa.v)
    InvCorU.grid[,,r] <- chol2inv(chol(CorU.grid[,,r]))
    InvCorV.grid[,,r] <- chol2inv(chol(CorV.grid[,,r]))
  }
  
  if(is.numeric(fix_rho)){
    rho_u_ind <- rho_v_ind <- which(rho_seq == fix_rho)
  } else if(isFALSE(fix_rho)) {
    rho_u_ind <- rho_v_ind <- ceiling((1+nr)/2)
  }
  
  rho.u <- rho_seq[rho_u_ind]
  rho.v <- rho_seq[rho_v_ind]
  
  InvCorU <- InvCorU.grid[,,rho_u_ind]
  InvCorV <- InvCorV.grid[,,rho_v_ind]
  
  sig2u <- sig2v <- 1
  phi <- 0
  u <- v <- rnorm(G)
  L <- as.vector(colSums(t(Z)*delta) + eta + v + phi*u)
  psi <- 0.1
  
  
  # Keep track of stuff
  varnames <- c("eta", paste("delta", cov.names), "alpha0", paste("beta0", cov.names), "alpha1", paste("beta1", cov.names),
                "phi", "rho.u", "rho.v", "sig2u", "sig2v", "kappa.u", "kappa.v", "psi", "sig2y")
  keepers <- matrix(NA, iters, length(varnames))
  colnames(keepers) <- varnames
  
  ATE_vec <- rep(NA, iters)
  u_mn <- v_mn <- 0
  u_var <- v_var <- 0
  
  
  # MCMC setup
  
  ## Intensities
  
  att.HMC <- acc.HMC <- 0
  
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
    #########################################
    ## Parameters involving normal layer Y ##
    #########################################
    
    # alpha0 
    u.vec <- as.vector(H%*%u)
    Cov.y <- solve(t(X_tot)%*%X_tot/sig2y + diag(ncol(X_tot))/pri_sd_beta^2)
    mean.y <- t(X_tot)%*%(Y-u.vec)/sig2y
    reg_coef <- as.vector(rmvnorm(1, Cov.y%*%mean.y, Cov.y))
    Xb <- as.vector(X_tot%*%reg_coef)
    
    alpha0 <- as.vector(reg_coef)[1]
    alpha1 <- as.vector(reg_coef)[2]
    beta0 <- as.vector(reg_coef)[3:(p+2)]
    beta1 <- as.vector(reg_coef)[(p+3):(2*p+2)]
    
    # sig2y
    QF.y <- sum((Y-Xb-u.vec)^2)
    sig2y <- 1/rgamma(1, n/2+a, QF.y/2+b)
    
    
    # u
    mu_u <- as.vector(t(H)%*%(Y-Xb))/sig2y
    Qu <- diag(N/sig2y)
    QQ <- InvCorU/sig2u
    
    Zb <- eta + Z%*%delta
    mu_v <- (L-Zb-v)*phi/psi
    Qv <- diag(G)*phi^2/psi
    
    C <- chol2inv(chol(Qu+Qv+QQ))
    bb <- mu_u + mu_v
    u <- C%*%bb + t(chol(C))%*%rnorm(G)
    
    # Variance parameters for U
    QF.u <- as.numeric(t(u)%*%InvCorU%*%u)
    sig2u <- 1/rgamma(1, G/2 + a, QF.u/2 + b)
    
    
    # rho.u
    if(isFALSE(fix_rho)){
      curlp <- sum(log(diag(t(chol(InvCorU))))) - t(u)%*%InvCorU%*%u/(2*sig2u)
      
      can_rho_u_ind <- rho_u_ind + 2*rbinom(1, 1, .5)-1
      if(can_rho_u_ind > 0 & can_rho_u_ind <= nr){
        canInvCorU <- InvCorU.grid[,,can_rho_u_ind]
        canlp <- sum(log(diag(t(chol(canInvCorU))))) - t(u)%*%canInvCorU%*%u/(2*sig2u)
        
        if(runif(1) < exp(canlp-curlp)){
          rho_u_ind <- can_rho_u_ind
          rho.u <- rho_seq[rho_u_ind]
          InvCorU <- canInvCorU
        }
      }
    }
    
    
    ##########################
    # The point process part #
    ##########################
    
    # log intensity L
    Zb <- as.vector(Z%*%delta) + eta
    logU <- function(q){
      sum((q - (Zb+v+phi*u))^2)/(2*psi) - sum(dpois(N, exp(q), TRUE))
    }
    
    gradU <- function(q){
      (q - (Zb+v+phi*u))/psi - (N - exp(q))
    }
    
    att.HMC[1] <- att.HMC[1] + 1
    new_L <- HMC_naive(logU, gradU, tau_L, Leap, L)
    if(new_L[[1]] == "accept") {
      acc.HMC[1] <- acc.HMC[1] + 1
      L <- new_L[[2]]
    }
    
    
    # v
    mu_v <- (L-Zb-phi*u)/psi
    Qv <- diag(G)/psi
    
    spec_comp <- eigen(InvCorV)
    QQ <- diag(spec_comp$values)/sig2v
    VV <- spec_comp$vectors
    
    SS <- diag(1/diag(Qv + QQ))
    C <- VV%*%SS%*%t(VV)
    v <- C%*%mu_v + t(chol(C))%*%rnorm(G)
    
    
    # eta, phi, delta
    Z_tot <- cbind(rep(1, G), Z, u) 
    b.eta <- t(Z_tot)%*%(L-v)/psi
    Q.eta <- solve(t(Z_tot)%*%Z_tot/psi + diag(ncol(Z_tot))/pri_sd_delta^2)
    reg_coef_L <- Q.eta%*%b.eta + t(chol(Q.eta))%*%rnorm(ncol(Z_tot))
    
    eta <- reg_coef_L[1]
    delta <- reg_coef_L[2:(p+1)]
    phi <- reg_coef_L[p+2]
    
    Zb <- as.vector(eta + Z%*%delta)
    lambda <- exp(Zb + v + phi*u)
    
    
    # psi
    QF.L <- sum((L-Zb-v-phi*u)^2) 
    psi <- 1/rgamma(1, G/2+a, QF.L/2+b)
    
    
    # sig2v
    QF.v <- as.numeric(t(v)%*%InvCorV%*%v)
    sig2v <- 1/rgamma(1, G/2 + a, QF.v/2 + b)
    
    
    # rho.v
    if(isFALSE(fix_rho)){
      curlp <- sum(log(diag(t(chol(InvCorV))))) - t(v)%*%InvCorV%*%v/(2*sig2v)
      
      can_rho_v_ind <- rho_v_ind + 2*rbinom(1, 1, .5)-1
      if(can_rho_v_ind > 0 & can_rho_v_ind <= nr){
        canInvCorV <- InvCorV.grid[,,can_rho_v_ind]
        canlp <- sum(log(diag(t(chol(canInvCorV))))) - t(v)%*%canInvCorV%*%v/(2*sig2v)
        
        if(runif(1)<exp(canlp-curlp)){
          rho_v_ind <- can_rho_v_ind
          rho.v <- rho_seq[rho_v_ind]
          InvCorV <- canInvCorV
        }
      }
    }
    
    
    ##################################
    ## Tuning MCMC hyper-parameters ##
    ##################################
    
    # Step size tuning
    if(iter<burn){for(k in 1:length(tau_L)){if(att.HMC[k] > 50){
      if(acc.HMC[k]/att.HMC[k] < 0.7){tau_L[k] <- tau_L[k]*0.8}
      if(acc.HMC[k]/att.HMC[k] > 0.9){tau_L[k] <- tau_L[k]*1.2}
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
      keepers[iter,] <- c(eta, delta, alpha0, beta0, alpha1, beta1, phi,
                          rho.u, rho.v, sig2u, sig2v, kappa.u, kappa.v,
                          psi, sig2y)
      ATE_vec[iter] <- alpha1 + mean(Z%*%beta1)
      
    } else {
      if(iter%%thin == 0) {
        keepers[burn+(iter-burn)/thin,] <- c(eta, delta, alpha0, beta0, alpha1, beta1, phi,
                                             rho.u, rho.v, sig2u, sig2v, kappa.u, kappa.v,
                                             psi, sig2y)
        
        ATE_vec[burn+(iter-burn)/thin] <- alpha1 + mean(Z%*%beta1)
        
        u_mn <- u_mn + u/(iters-burn)
        v_mn <- v_mn + v/(iters-burn)
        
        u_var <- u_var + u^2/(iters-burn)
        v_var <- v_var + v^2/(iters-burn)
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
                 uv_mn = cbind(u_mn, v_mn),
                 uv_var = cbind(u_var-u_mn^2, v_var-v_mn^2),
                 acc_HMC = acc.HMC/att.HMC,
                 acc_rate_rho = acc.rho/att.rho,
                 acc_rate_kappa = acc.kappa/att.kappa,
                 time = (tock-tick)/60) # time is minute scale
  
  return(output)
}

# ------------------------------------------------------------------------------

# Run the proposed model by Son et. al (2026)
# Arguments:
#   @Y             Observed outcome vector
#   @Tr            Treatment status vector
#   @N0            The number of controlled locations in each cell of the discretized domain
#   @N1            The number of treated locations in each cell of the discretized domain
#   @domain        G by 2 matrix containing the centroids of the grid cells
#   @X             N by p covariate matrix for observations
#   @Z             G by p covariate matrix for grid cells 
#   @H             N by G matrix with (i,g) entry 1 if ith location belongs to gth cell (i = 1,...,N and g = 1,...,G)
#   @L             The number of leap frog steps
#   @tau           Leapfrog step size
#   @center.X      Logical whether to center and scale X matrix
#   @center.Z      Logical whether to center and scale Z matrix
#   @update.gamma  Logical whether to update or fix gamma (LMC) parameters
#   @pri_sd_phi    Prior sd for phi (preferential sampling parameter)
#   @pri_sd_beta   Prior sd for beta (regression coefficients of the outcome)
#   @a             Shape paramter of inverse gamma priors
#   @b             Scale paramter of inverse gamma priors
#   @pri_sd_delta  Prior sd for delta (regression coefficients of the point process)
#   @pref_samp     Logical. If FALSE, the model reduces to a geostatistical model without point processes
#   @fix_rho       Logical whether to update or fix rho, spatial dependence
#   @iters         The number of MCMC samples after burn-in
#   @burn          The number of burn-in samples
#   @update        Print progress every this many iterations. Ignored if verbose = FALSE
#   @thin          Keep every jth sample to reduce autocorrelation. Default: 1
#   @verbose       Logical whether to print progress messages
#   @HMC           Logical whether to use HMC or Metropolis samplers without adaptation
#   @ppp           Logical whether to use all grid cells or not
#   @euclidean     Logical whether to use euclidean distances or pairwise great circle distances
#   @fix_kappa.u   Logical whether to update or fix the spatial smoothness of U process
#   @fix_kappa.v   Logical whether to update or fix the spatial smoothness of V process
#   @rho_seq       The sequence of candidate rhos for discretized Metropolis sampler
#   @kappa_mn      Prior mean of the spatial smoothness parameters
#   @kappa_sd      Prior sd of the spatial smoothness parameters
Mat.PO.RE <-  function(Y, Tr, N0, N1, domain, X, Z, H, L = 20, tau = rep(1/L, 2),
                       center.X = FALSE, center.Z = FALSE, update.gamma = TRUE,
                       pri_sd_phi = 10, pri_sd_beta = 10, a = 0.1, b = 0.1, 
                       pri_sd_delta = 10, pref_samp = TRUE, fix_rho = FALSE,
                       iters = 20000, burn = 5000, update = 2000, thin = 1,
                       verbose = FALSE, HMC = TRUE, ppp = NULL,
                       euclidean = TRUE, fix_kappa.u = FALSE, fix_kappa.v = FALSE,
                       rho_seq = seq(0.01, 0.2, by = 0.01), kappa_mn = log(0.5), kappa_sd = 1){
  library(Matrix)
  library(MASS)
  library(spam)
  library(geoR)
  
  tick <- proc.time()[3]
  
  if(is.null(ppp)) {ppp <- rep(TRUE, nrow(Z))}
  iters_thin <- (iters-burn)*thin
  X_center <- as.matrix(X)
  Z_center <- Z_mean <- as.matrix(Z)
  
  if(center.X) {for(p in 1:ncol(Z_mean)){Z_mean[,p] <- Z[,p] - mean(X[,p])}}
  if(center.X) {X_center <- scale(X_center, center = TRUE, scale = FALSE)}
  if(center.Z) {Z_center <- scale(Z_center, center = TRUE, scale = FALSE)}
  
  Z_center <- Z_center[ppp,]
  Z_mean <- Z_mean[ppp,]
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
  n <- nrow(X)
  
  # distance matrix
  if(euclidean) {
    distMat <- as.matrix(dist(domain))
  } else {
    distMat <- fields::rdist.earth(domain, domain, miles = FALSE)
  }
  diag(distMat) <- 0
  
  # Initial values
  
  lin.mod <- lm(Y~Tr+X_center)
  glm.mod0 <- summary(glm(N0~Z_center, family="poisson"))
  glm.mod1 <- summary(glm(N1~Z_center, family="poisson"))
  
  eta0 <- as.vector(glm.mod0$coefficients[,1])[1]
  eta1 <- as.vector(glm.mod1$coefficients[,1])[1]
  
  delta0 <- as.vector(glm.mod0$coefficients[,1])[-1]
  delta1 <- as.vector(glm.mod1$coefficients[,1])[-1]
  
  alpha0 <- as.vector(lin.mod$coefficients)[1]
  alpha1 <- sum(as.vector(lin.mod$coefficients)[c(1,2)])
  
  beta0 <- beta1 <- as.vector(lin.mod$coefficients)[-c(1,2)]
  
  sig2y0 <- sum(lin.mod$residuals^2)/sum(N)
  sig2y1 <- sig2y0
  
  # Precomputes Matern covariance with rho and kappa grids 
  kappa.u <- kappa.v <- exp(kappa_mn)
  
  nr <- length(rho_seq)
  CorU.grid <- array(0, c(G, G, nr))
  CorV.grid <- array(0, c(G, G, nr))
  InvCorU.grid <- array(0, c(G, G, nr))
  InvCorV.grid <- array(0, c(G, G, nr))
  
  for(r in 1:nr){
    CorU.grid[,,r] <- corfx(distMat, rho_seq[r], kappa.u)
    CorV.grid[,,r] <- corfx(distMat, rho_seq[r], kappa.v)
    InvCorU.grid[,,r] <- chol2inv(chol(CorU.grid[,,r]))
    InvCorV.grid[,,r] <- chol2inv(chol(CorV.grid[,,r]))
  }
  
  if(is.numeric(fix_rho)){
    rho_u_ind <- rho_v_ind <- which(rho_seq == fix_rho)
  } else if(isFALSE(fix_rho)) {
    rho_u_ind <- rho_v_ind <- ceiling((1+nr)/2)
  }
  
  rho.u <- rho_seq[rho_u_ind]
  rho.v <- rho_seq[rho_v_ind]
  
  InvCorU <- InvCorU.grid[,,rho_u_ind]
  InvCorV <- InvCorV.grid[,,rho_v_ind]
  
  sig2u0 <- sig2u1 <- sig2v0 <- sig2v1 <- 1
  u0t <- u1t <- v0t <- v1t <- rep(0, G)
  
  gamma.u <- gamma.v <- 0.5
  phi0 <- phi1 <- 0
  
  u0 <- u0t
  u1 <- u1t + gamma.u*u0t
  
  v0 <- v0t
  v1 <- v1t + gamma.v*v0t
  
  L0 <- as.vector(colSums(t(Z_center)*delta0) + eta0 + v0 + phi0*u0)
  L1 <- as.vector(colSums(t(Z_center)*delta1) + eta1 + v1 + phi1*u1)
  
  psi0 <- psi1 <- 0.1
  
  
  # Keep track of stuff
  
  keepers <- matrix(NA, iters, 2*p + 2*q + 18 + 2)
  colnames(keepers) <- c("eta0", paste("delta0", cov.names), "eta1", paste("delta1", cov.names),
                         "alpha0", paste("beta0", cov.names), "alpha1", paste("beta1", cov.names),
                         "rho.u", "rho.v", "phi0", "phi1", "gamma.u", "gamma.v", "sig2u0", "sig2u1", 
                         "sig2v0", "sig2v1", "kappa.u", "kappa.v", "psi0", "psi1", "sig2y0", "sig2y1")
  
  ATE_vec <- rep(NA, iters)
  ATE_no_RE_vec <- rep(NA, iters)
  
  prop.score <- posit.vec <- local_effect <- local_var <- 0
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
    
    Y0[na.y0] <- rnorm(sum(N1), (X_center%*%beta0 + u0.vec)[na.y0], sqrt(sig2y0)) + alpha0
    Y1[na.y1] <- rnorm(sum(N0), (X_center%*%beta1 + u1.vec)[na.y1], sqrt(sig2y1)) + alpha1
    
    
    #########################################
    ## Parameters involving normal layer Y ##
    #########################################
    
    
    # alpha0 
    u0.vec <- as.vector(H%*%u0)
    Cov.y <- 1/(n/sig2y0 + 1/pri_sd_beta^2)
    mean.y <- sum(Y0-u0.vec-X_center%*%beta0)/sig2y0
    alpha0 <- rnorm(1, Cov.y*mean.y, sqrt(Cov.y))
    
    # alpha1 
    u1.vec <- as.vector(H%*%u1)
    Cov.y <- 1/(n/sig2y1 + 1/pri_sd_beta^2)
    mean.y <- sum(Y1-u1.vec-X_center%*%beta1)/sig2y1
    alpha1 <- rnorm(1, Cov.y*mean.y, sqrt(Cov.y))
    
    # beta0
    Qbeta <- solve(t(X_center)%*%X_center/sig2y0 + diag(p)/pri_sd_beta^2)
    bbeta <- t(X_center)%*%(Y0-alpha0-u0.vec)/sig2y0
    beta0 <- Qbeta%*%bbeta + t(chol(Qbeta))%*%rnorm(ncol(X_center))
    
    # beta1
    Qbeta <- solve(t(X_center)%*%X_center/sig2y1 + diag(p)/pri_sd_beta^2)
    bbeta <- t(X_center)%*%(Y1-alpha1-u1.vec)/sig2y1
    beta1 <- Qbeta%*%bbeta + t(chol(Qbeta))%*%rnorm(ncol(X_center))
    
    Xb0 <- as.vector(X_center%*%beta0) + alpha0
    Xb1 <- as.vector(X_center%*%beta1) + alpha1
    
    # sig2y0
    QF.y <- sum((Y0-Xb0-u0.vec)^2)
    sig2y0 <- 1/rgamma(1, n/2+a, QF.y/2+b)
    
    # sig2y1
    QF.y <- sum((Y1-Xb1-u1.vec)^2)
    sig2y1 <- 1/rgamma(1, n/2+a, QF.y/2+b)
    
    
    #############################################
    ## Latent spatial random effects U0 and U1 ##
    #############################################
    
    Xb0 <- as.vector(X_center%*%beta0) + alpha0
    Xb1 <- as.vector(X_center%*%beta1) + alpha1
    
    # u0.tilde
    u1t.vec <- as.vector(H%*%u1t)
    mu0u <- as.vector(t(H)%*%(Y0-Xb0))/sig2y0
    mu1u <- as.vector(t(H)%*%(Y1-Xb1-u1t.vec))*gamma.u/sig2y1
    
    Q0u <- diag(N/sig2y0)
    Q1u <- diag(N*gamma.u^2/sig2y1)
    QQ <- InvCorU/sig2u0
    
    if(pref_samp){
      Zb0 <- as.vector(Z_center%*%delta0) + eta0
      Zb1 <- as.vector(Z_center%*%delta1) + eta1
      
      mu0v <- (L0-Zb0-v0)*phi0/psi0
      mu1v <- (L1-Zb1-v1-phi1*u1t)*(phi1*gamma.u)/psi1
      
      Q0v <- diag(G)*phi0^2/psi0 
      Q1v <- diag(G)*(phi1*gamma.u)^2/psi1
      
      C <- chol2inv(chol(Q0u+Q1u+Q0v+Q1v+QQ))
      bb <- mu0u + mu1u + mu0v + mu1v
      u0t <- C%*%bb + t(chol(C))%*%rnorm(G)
    } else {
      C <- chol2inv(chol(Q0u+Q1u+QQ))
      bb <- mu0u + mu1u
      u0t <- C%*%bb + t(chol(C))%*%rnorm(G)
    }
    
    
    # u1.tilde
    u0t.vec <- as.vector(H%*%u0t)
    mu1u <- as.vector(t(H)%*%(Y1-Xb1-gamma.u*u0t.vec))/sig2y1
    Q1u <- diag(N/sig2y1)
    QQ <- InvCorU/sig2u1
    
    if(pref_samp){
      mu1v <- (L1-Zb1-v1-(phi1*gamma.u)*u0t)*phi1/psi1
      Q1v <- diag(G)*phi1^2/psi1
      C <- chol2inv(chol(Q1u+Q1v+QQ))
      bb <- mu1u + mu1v
      u1t <- C%*%bb + t(chol(C))%*%rnorm(G)
    } else {
      C <- chol2inv(chol(Q1u+QQ))
      bb <- mu1u
      u1t <- C%*%bb + t(chol(C))%*%rnorm(G)
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
      curlp <- 
        2*sum(log(diag(t(chol(InvCorU)))))-
        t(u0t)%*%InvCorU%*%u0t/(2*sig2u0)-
        t(u1t)%*%InvCorU%*%u1t/(2*sig2u1)
      
      can_rho_u_ind <- rho_u_ind + 2*rbinom(1, 1, .5)-1
      if(can_rho_u_ind > 0 & can_rho_u_ind <= nr){
        canInvCorU <- InvCorU.grid[,,can_rho_u_ind]
        canlp <- 
          2*sum(log(diag(t(chol(canInvCorU)))))-
          t(u0t)%*%canInvCorU%*%u0t/(2*sig2u0)-
          t(u1t)%*%canInvCorU%*%u1t/(2*sig2u1)
        
        if(runif(1) < exp(canlp-curlp)){
          rho_u_ind <- can_rho_u_ind
          rho.u <- rho_seq[rho_u_ind]
          InvCorU <- canInvCorU
        }
      }
    }
    
    # kappa.u
    
    
    
    if(pref_samp){
      #######################
      # The intensity parts #
      #######################
      
      Zb0 <- as.vector(Z_center%*%delta0) + eta0
      Zb1 <- as.vector(Z_center%*%delta1) + eta1
      
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
      spec_comp <- eigen(InvCorV)
      QQ <- diag(spec_comp$values)/sig2v0
      VV <- spec_comp$vectors
      
      SS <- diag(1/diag(Q0v + Q1v + QQ))
      C <- VV%*%SS%*%t(VV)
      bb <- mu0v + mu1v
      v0t <- C%*%bb + t(chol(C))%*%rnorm(G)
      
      
      # v1.tilde
      mu1v <- (L1-Zb1-gamma.v*v0t-phi1*u1)/psi1
      Q1v <- diag(G)/psi1 
      QQ <- diag(spec_comp$values)/sig2v1
      SS <- diag(1/diag(Q1v + QQ))
      C <- VV%*%SS%*%t(VV)
      bb <- mu1v
      v1t <- C%*%bb + t(chol(C))%*%rnorm(G)
      
      
      # eta0, phi0
      Zu <- cbind(rep(1, G), u0) 
      b.eta0 <- t(Zu)%*%(L0-Z_center%*%delta0-v0)/psi0
      Q.eta0 <- solve(t(Zu)%*%Zu/psi0 + diag(ncol(Zu))/pri_sd_delta^2)
      etaphi0 <- Q.eta0%*%b.eta0 + t(chol(Q.eta0))%*%rnorm(ncol(Zu))
      eta0 <- etaphi0[1]
      phi0 <- etaphi0[2]
      
      
      # eta1, phi1, gamma.v
      Zu <- cbind(rep(1, G), u1, v0t)
      b.eta1 <- t(Zu)%*%(L1-Z_center%*%delta1-v1t)/psi1
      Q.eta1 <- solve(t(Zu)%*%Zu/psi1 + diag(ncol(Zu))/pri_sd_delta^2)
      etaphi1 <- Q.eta1%*%b.eta1 + t(chol(Q.eta1))%*%rnorm(ncol(Zu))
      eta1 <- etaphi1[1]
      phi1 <- etaphi1[2]
      gamma.v <- etaphi1[3]
      
      v0 <- v0t
      v1 <- v1t + gamma.v*v0t
      
      
      # delta0
      bdelta0 <- t(Z_center)%*%(L0-eta0-v0-phi0*u0)/psi0
      Qdelta0 <- solve(t(Z_center)%*%Z_center/psi0 + diag(q)/pri_sd_delta^2)
      delta0 <- Qdelta0%*%bdelta0 + t(chol(Qdelta0))%*%rnorm(ncol(Z_center))
      
      
      # delta1
      bdelta1 <- t(Z_center)%*%(L1-eta1-v1-phi1*u1)/psi1 
      Qdelta1 <- solve(t(Z_center)%*%Z_center/psi1 + diag(q)/pri_sd_delta^2)
      delta1 <- Qdelta1%*%bdelta1 + t(chol(Qdelta1))%*%rnorm(ncol(Z_center))
      
      
      Zb0 <- as.vector(Z_center%*%delta0) + eta0
      Zb1 <- as.vector(Z_center%*%delta1) + eta1
      
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
        curlp <- 
          2*sum(log(diag(t(chol(InvCorV)))))-
          t(v0t)%*%InvCorV%*%v0t/(2*sig2v0)-
          t(v1t)%*%InvCorV%*%v1t/(2*sig2v1)
        
        can_rho_v_ind <- rho_v_ind + 2*rbinom(1, 1, .5)-1
        if(can_rho_v_ind > 0 & can_rho_v_ind <= nr){
          canInvCorV <- InvCorV.grid[,,can_rho_v_ind]
          canlp <- 
            2*sum(log(diag(t(chol(canInvCorV)))))-
            t(v0t)%*%canInvCorV%*%v0t/(2*sig2v0)-
            t(v1t)%*%canInvCorV%*%v1t/(2*sig2v1)
          
          if(runif(1)<exp(canlp-curlp)){
            rho_v_ind <- can_rho_v_ind
            rho.v <- rho_seq[rho_v_ind]
            InvCorV <- canInvCorV
          }
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
      keepers[iter,] <- c(eta0, delta0, eta1, delta1, 
                          alpha0, beta0, alpha1, beta1,
                          rho.u, rho.v, phi0, phi1, 
                          gamma.u, gamma.v, sig2u0, sig2u1, 
                          sig2v0, sig2v1, kappa.u, kappa.v,
                          psi0, psi1, sig2y0, sig2y1)
      
      ATE_vec[iter] <- alpha1 - alpha0 + mean(Z_mean%*%(beta1-beta0)) + mean(u1 - u0)
      ATE_no_RE_vec[iter] <- alpha1 - alpha0 + mean(Z_mean%*%(beta1-beta0))
      
    } else {
      if(iter%%thin == 0) {
        keepers[burn+(iter-burn)/thin,] <- c(eta0, delta0, eta1, delta1, 
                                             alpha0, beta0, alpha1, beta1,
                                             rho.u, rho.v, phi0, phi1, 
                                             gamma.u, gamma.v, sig2u0, sig2u1, 
                                             sig2v0, sig2v1, kappa.u, kappa.v,
                                             psi0, psi1, sig2y0, sig2y1)
        
        ATE_vec[burn+(iter-burn)/thin] <- alpha1 - alpha0 + mean(Z_mean%*%(beta1-beta0)) + mean(u1 - u0)
        ATE_no_RE_vec[burn+(iter-burn)/thin] <- alpha1 - alpha0 + mean(Z_mean%*%(beta1-beta0))
        
        u0_mn <- u0_mn + u0/(iters-burn)
        u1_mn <- u1_mn + u1/(iters-burn)
        v0_mn <- v0_mn + v0/(iters-burn)
        v1_mn <- v1_mn + v1/(iters-burn)
        
        u0_var <- u0_var + u0^2/(iters-burn)
        u1_var <- u1_var + u1^2/(iters-burn)
        v0_var <- v0_var + v0^2/(iters-burn)
        v1_var <- v1_var + v1^2/(iters-burn)
        
        posit.vec <- posit.vec + as.numeric((alpha1 - alpha0 + Z_mean%*%(beta1-beta0) + u1 - u0)>0)/(iters-burn)
        local_effect <- local_effect + (alpha1-alpha0 + Z_mean%*%(beta1-beta0) + u1-u0)/(iters-burn)
        local_var <- local_var + (alpha1-alpha0 + Z_mean%*%(beta1-beta0) + u1-u0)^2/(iters-burn)
        
        if(pref_samp){
          prop.score <- prop.score + ((lambda1)/(lambda0 + lambda1))/(iters-burn)
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
                 ATE_no_RE = ATE_no_RE_vec,
                 prop.score = prop.score,
                 posit.prob = posit.vec,
                 uv_mn = cbind(u0_mn, u1_mn, v0_mn, v1_mn),
                 uv_var = cbind(u0_var-u0_mn^2, u1_var-u1_mn^2, v0_var-v0_mn^2, v1_var-v1_mn^2),
                 local_effect = local_effect,
                 local_var = local_var - local_effect^2,
                 acc_HMC = acc.HMC/att.HMC,
                 acc_rate_rho = acc.rho/att.rho,
                 acc_rate_kappa = acc.kappa/att.kappa,
                 time = (tock-tick)/60) # time is minute scale
  
  return(output)
}

# ------------------------------------------------------------------------------

# Run the proposed model with fixing beta0 = beta1 = beta by Son et. al (2026)
# Arguments:
#   @Y             Observed outcome vector
#   @Tr            Treatment status vector
#   @N0            The number of controlled locations in each cell of the discretized domain
#   @N1            The number of treated locations in each cell of the discretized domain
#   @domain        G by 2 matrix containing the centroids of the grid cells
#   @X             N by p covariate matrix for observations
#   @Z             G by p covariate matrix for grid cells 
#   @H             N by G matrix with (i,g) entry 1 if ith location belongs to gth cell (i = 1,...,N and g = 1,...,G)
#   @L             The number of leap frog steps
#   @tau           Leapfrog step size
#   @center.X      Logical whether to center and scale X matrix
#   @center.Z      Logical whether to center and scale Z matrix
#   @update.gamma  Logical whether to update or fix gamma (LMC) parameters
#   @pri_sd_phi    Prior sd for phi (preferential sampling parameter)
#   @pri_sd_beta   Prior sd for beta (regression coefficients of the outcome)
#   @a             Shape paramter of inverse gamma priors
#   @b             Scale paramter of inverse gamma priors
#   @pri_sd_delta  Prior sd for delta (regression coefficients of the point process)
#   @pref_samp     Logical. If FALSE, the model reduces to a geostatistical model without point processes
#   @fix_rho       Logical whether to update or fix rho, spatial dependence
#   @iters         The number of MCMC samples after burn-in
#   @burn          The number of burn-in samples
#   @update        Print progress every this many iterations. Ignored if verbose = FALSE
#   @thin          Keep every jth sample to reduce autocorrelation. Default: 1
#   @verbose       Logical whether to print progress messages
#   @HMC           Logical whether to use HMC or Metropolis samplers without adaptation
#   @ppp           Logical whether to use all grid cells or not
#   @euclidean     Logical whether to use euclidean distances or pairwise great circle distances
#   @fix_kappa.u   Logical whether to update or fix the spatial smoothness of U process
#   @fix_kappa.v   Logical whether to update or fix the spatial smoothness of V process
#   @rho_seq       The sequence of candidate rhos for discretized Metropolis sampler
#   @kappa_mn      Prior mean of the spatial smoothness parameters
#   @kappa_sd      Prior sd of the spatial smoothness parameters
Mat.PO.share <-  function(Y, Tr, N0, N1, domain, X, Z, H, L = 20, tau = rep(1/L, 2),
                          center.X = TRUE, center.Z = TRUE, update.gamma = TRUE,
                          pri_sd_phi = 10, pri_sd_beta = 10, a = 0.1, b = 0.1, 
                          pri_sd_delta = 10, pref_samp = TRUE, fix_rho = FALSE,
                          iters = 20000, burn = 5000, update = 2000, thin = 1,
                          verbose = FALSE, HMC = FALSE, ppp = rep(TRUE, nrow(Z)),
                          euclidean = FALSE, rho_mn = 0, rho_sd = 1, fix_kappa.u = TRUE,
                          fix_kappa.v = TRUE){
  library(Matrix)
  library(MASS)
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
  #M <- as(diag(m), "sparseMatrix")
  
  # distance matrix
  if(euclidean) {
    distMat <- as.matrix(dist(domain))
  } else {
    distMat <- fields::rdist.earth(domain, domain, miles = FALSE)
  }
  diag(distMat) <- 0
  
  # Initial values
  
  lin.mod <- lm(Y~Tr+X_center)
  glm.mod <- summary(glm(N0~Z_center, family="poisson"))
  
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
  phi0 <- phi1 <- 0.1
  
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
  ATE_no_RE_vec <- rep(NA, iters)
  
  prop.score <- prop.score.obs <- posit.vec <- 0
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
      ATE_no_RE_vec[iter] <- alpha1 - alpha0
      
    } else {
      if(iter%%thin == 0) {
        keepers[burn+(iter-burn)/thin,] <- c(eta0, eta1, delta, alpha0, alpha1, beta,
                                             rho.u, rho.v, phi0, phi1, gamma.u, gamma.v, 
                                             sig2u0, sig2u1, sig2v0, sig2v1, kappa.u, kappa.v,
                                             psi0, psi1, sig2y0, sig2y1)
        
        ATE_vec[burn+(iter-burn)/thin] <- alpha1 - alpha0 + mean(u1 - u0)
        ATE_no_RE_vec[burn+(iter-burn)/thin] <- alpha1 - alpha0
        
        u0_mn <- u0_mn + u0/(iters-burn)
        u1_mn <- u1_mn + u1/(iters-burn)
        v0_mn <- v0_mn + v0/(iters-burn)
        v1_mn <- v1_mn + v1/(iters-burn)
        
        u0_var <- u0_var + u0^2/(iters-burn)
        u1_var <- u1_var + u1^2/(iters-burn)
        v0_var <- v0_var + v0^2/(iters-burn)
        v1_var <- v1_var + v1^2/(iters-burn)
        
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
                 ATE_no_RE = ATE_no_RE_vec,
                 prop.score = prop.score,
                 posit.prob = posit.vec,
                 uv_mn = cbind(u0_mn, u1_mn, v0_mn, v1_mn),
                 uv_var = cbind(u0_var-u0_mn^2, u1_var-u1_mn^2, v0_var-v0_mn^2, v1_var-v1_mn^2),
                 acc_HMC = acc.HMC/att.HMC,
                 acc_rate_rho = acc.rho/att.rho,
                 acc_rate_kappa = acc.kappa/att.kappa,
                 time = (tock-tick)/60) # time is minute scale
  
  return(output)
}

# ------------------------------------------------------------------------------

# Run a simulation with Naive, Shared, Full, PSA-B, PSA-G models under various data generating processes (DGP)
# Arguments:
#   @nonGauss     logical whether to run models with non-Gaussian DGP
#   @nonstat      logical whether to run models with non-stationary DGP
#   @phi          Run models under stationary & Gaussian DGP with different degree of preferential sampling
#   @lambda       Run models under stationary & Gaussian DGP with different number of obs per cell
#   @rho          Run models under stationary & Gaussian DGP with different degree of spatial dependence
#   @gamma.u      Run models under stationary & Gaussian DGP with different degree of LMC
#   @df           Degrees of freedom of B-splines for propensity score adjustment
#   @iters        The number of MCMC samples after burn-in
#   @burn         The number of burn-in samples
runModel_matern <- function (nonGauss = FALSE, nonstat = FALSE, phi = 2/3, lambda = 5, 
                             rho = 0.1, gamma.u = -0.5, df = 5, iters = 120000, burn = 50000) 
{
  library(Matrix)
  library(geoR)
  
  n.grid <- 20
  s <- (2 * (1:n.grid) - 1)/(2 * n.grid)
  grid <- expand.grid(s, s)
  G <- nrow(grid)
  resolution <- s[2] - s[1]
  distMat <- as.matrix(dist(grid))
  diag(distMat) <- 0
  
  alpha0 <- 2
  alpha1 <- 4
  beta0 <- c(1, 1)
  beta1 <- c(-1, -1)
  delta0 <- c(1, 1)
  delta1 <- c(-1, -1)
  gamma.u <- gamma.u
  sig2u0 <- 1
  sig2u1 <- 1
  gamma.v <- 0.5
  sig2v0 <- 1
  sig2v1 <- 1
  sig2y0 <- sig2y1 <- 0.1
  psi0 <- psi1 <- 0.1
  rho <- rho
  kappa <- 0.5
  phi0 <- phi
  phi1 <- 1.5 * phi0
  lambda <- lambda
  ru <- gamma.u * sig2u0/(sqrt(sig2u0) * sqrt(sig2u1 + gamma.u^2 * sig2u0))
  rv <- gamma.v * sig2v0/(sqrt(sig2v0) * sqrt(sig2v1 + gamma.v^2 * sig2v0))
  delta0.new <- delta0 + phi0 * beta0
  delta1.new <- delta1 + phi1 * beta1
  
  CorMat <- corfx(distMat, rho, kappa)
  u0t <- as.vector(t(chol(sig2u0 * CorMat)) %*% rnorm(G))
  u1t <- as.vector(t(chol(sig2u1 * CorMat)) %*% rnorm(G))
  v0t <- as.vector(t(chol(sig2v0 * CorMat)) %*% rnorm(G))
  v1t <- as.vector(t(chol(sig2v1 * CorMat)) %*% rnorm(G))
  
  Zcor <- corfx(distMat, 0.05, 0.5)
  Z <- cbind(t(chol(Zcor)) %*% rnorm(G, 0, sqrt(0.5)), t(chol(Zcor)) %*% rnorm(G, 0, sqrt(0.5)))
  colnames(Z) <- c("V1", "V2")
  
  if (nonstat) {
    grid_ns <- grid
    grid_ns[, 2] <- grid_ns[, 2]^2
    distMat_ns <- as.matrix(dist(grid_ns))
    diag(distMat_ns) <- 0
    CorMat_ns <- corfx(distMat_ns, rho, kappa)
    u0t <- as.vector(t(chol(sig2u0 * CorMat)) %*% rnorm(G))
    u1t <- as.vector(t(chol(sig2u1 * CorMat)) %*% rnorm(G))
    v0t <- as.vector(t(chol(sig2v0 * CorMat_ns)) %*% rnorm(G))
    v1t <- as.vector(t(chol(sig2v1 * CorMat_ns)) %*% rnorm(G))
  }
  
  u0 <- u0t
  u1 <- u1t + gamma.u * u0t
  v0 <- v0t
  v1 <- v1t + gamma.v * v0t
  
  lambda0 <- exp(as.vector(Z %*% delta0.new) + v0 + phi0 * u0 + rnorm(G, 0, sqrt(psi0)))
  if (nonGauss) {
    lambda0 <- exp(as.vector(Z %*% delta0.new) + v0 + phi0 * (ifelse(u0 > 0, u0, 0) - sqrt(sig2u0)/sqrt(2 * pi)) + rnorm(G, 0, sqrt(psi0)))
  }
  eta0 <- log(lambda/mean(lambda0))
  N0 <- rpois(n = G, lambda = exp(eta0) * lambda0)
  
  lambda1 <- exp(as.vector(Z %*% delta1.new) + v1 + phi1 * u1 + rnorm(G, 0, sqrt(psi1)))
  if (nonGauss) {
    sigma1 <- sig2u1 + gamma.u^2 * sig2u0
    lambda1 <- exp(as.vector(Z %*% delta1.new) + v1 + phi1 * (ifelse(u1 > 0, u1, 0) - sqrt(sigma1)/sqrt(2 * pi)) + rnorm(G, 0, sqrt(psi1)))
  }
  eta1 <- log(lambda/mean(lambda1))
  N1 <- rpois(n = G, lambda = exp(eta1) * lambda1)
  
  N <- N0 + N1
  X <- c()
  Y <- c()
  Tr <- c()
  grid.ind <- c()
  for (i in 1:G) {
    Y0 <- rnorm(N0[i], alpha0 + Z[i, ] %*% beta0 + u0[i], sqrt(sig2y0))
    Y1 <- rnorm(N1[i], alpha1 + Z[i, ] %*% beta1 + u1[i], sqrt(sig2y1))
    if (N[i] > 0) {
      X <- rbind(X, Z[rep(i, N[i]), , drop = FALSE])
      Y <- c(Y, c(Y0, Y1))
      Tr <- c(Tr, c(rep(0, N0[i]), rep(1, N1[i])))
      grid.ind <- c(grid.ind, rep(i, N[i]))
    }
  }
  
  H <- matrix(0, nrow = nrow(X), ncol = G)
  for (i in 1:nrow(X)) {
    H[i, grid.ind[i]] <- 1
  }
  H <- as(H, "sparseMatrix")
  
  true_ATE <- as.numeric(colMeans(Z) %*% (beta1 - beta0) + mean(u1 - u0) + (alpha1 - alpha0))
  true_ATE_obs <- as.numeric(colMeans(Z[N != 0, ]) %*% (beta1 - beta0) + mean((u1 - u0)[N != 0]) + (alpha1 - alpha0))
  true_ATE_sample <- as.numeric(colMeans(X) %*% (beta1 - beta0) + mean(H %*% (u1 - u0)) + (alpha1 - alpha0))
  
  full <- Mat.PO.RE(Y = Y, Tr = Tr, N0 = N0, N1 = N1, X = X, 
                    Z = Z, domain = grid, H = H, L = 20, pref_samp = TRUE, 
                    burn = burn, iters = iters, rho_seq = seq(0.01, 0.5, by = 0.005), 
                    fix_rho = FALSE, fix_kappa.u = TRUE, fix_kappa.v = TRUE, 
                    HMC = TRUE, center.X = FALSE, center.Z = FALSE, euclidean = TRUE, verbose = FALSE)
  
  naive <- Mat.PO.RE(Y = Y, Tr = Tr, N0 = N0, N1 = N1, X = X, 
                     Z = Z, domain = grid, H = H, L = 20, pref_samp = FALSE, 
                     burn = burn, iters = iters, rho_seq = seq(0.01, 0.5, by = 0.005), 
                     fix_rho = FALSE, fix_kappa.u = TRUE, fix_kappa.v = TRUE, 
                     HMC = TRUE, center.X = FALSE, center.Z = FALSE, euclidean = TRUE, verbose = FALSE)
  
  pati <- Pati(Y = Y, Tr = Tr, N = N, domain = grid, X = X, Z = Z, H = H, Leap = 20, 
               burn = burn, iters = iters, rho_seq = seq(0.01, 0.5, by = 0.005), 
               fix_rho = FALSE, fix_kappa.u = TRUE, fix_kappa.v = TRUE, euclidean = TRUE, verbose = FALSE)
  
  ps_adj_glm <- ps_adj_gp(Y = Y, 
                          Tr = Tr, 
                          domain = grid,
                          X = X, 
                          Z = Z, 
                          H = H,
                          N0 = N0,
                          N1 = N1,
                          burn = burn, 
                          iters = iters, 
                          df = df,
                          rho_seq = seq(0.01, 0.5, by = 0.005), 
                          spatial_glm = "glm",
                          fix_rho = FALSE, 
                          fix_kappa.u = TRUE, 
                          euclidean = TRUE, 
                          verbose = FALSE)
  
  ps_adj_brt <- ps_adj_gp(Y = Y, 
                          Tr = Tr, 
                          domain = grid,
                          X = X, 
                          Z = Z, 
                          H = H,
                          N0 = N0,
                          N1 = N1,
                          burn = burn, 
                          iters = iters, 
                          df = df,
                          rho_seq = seq(0.01, 0.5, by = 0.005), 
                          spatial_glm = "bart",
                          fix_rho = FALSE, 
                          fix_kappa.u = TRUE, 
                          euclidean = TRUE, 
                          verbose = FALSE)
  
  fit <- list(full = full, 
              naive = naive, 
              pati = pati, 
              ps_adj_glm = ps_adj_glm, 
              ps_adj_brt = ps_adj_brt, 
              True_ATE = true_ATE, 
              True_ATE_obs = true_ATE_obs, 
              True_ATE_sample = true_ATE_sample, 
              True_phi = phi, 
              True_rho = rho, 
              Mean_N0 = mean(N0), 
              Mean_N1 = mean(N1), 
              NS = nonstat, 
              NG = nonGauss)
  
  return(fit)
}
