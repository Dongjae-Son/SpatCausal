expit <- function(x){1/(1+exp(-x))}
logit <- function(x){log(x)-log(1-x)}
logit.beta <- function(y, a = 9, b = 1){dbeta(expit(y), a, b)*expit(-y)*expit(y)} # pdf of logit(X) where X~Beta(a,b)

corfx <- function(u, phi, kappa, matern=TRUE){
  if(!matern) {kappa <- 0.5}
  corr <- matern(u, phi, kappa)
  corr[u==0] <- 1
  return(corr)
}

ps_adj <- function(Y,
                   Tr,
                   domain,
                   X,
                   Z,
                   H,
                   N,
                   Leap = 20,
                   tau_L = 1/Leap,
                   pri_sd_beta = 10, 
                   a = 0.1, 
                   b = 0.1,
                   df = 5,
                   spatial_glm = c("glm", "bart", "spatial"),
                   euclidean = TRUE,
                   iters = 20000, 
                   burn = 5000, 
                   update = 2000, 
                   thin = 1,
                   verbose = FALSE, 
                   fix_rho = FALSE,
                   fix_kappa.u = TRUE,
                   rho_seq = seq(0.01, 0.2, by = 0.01), 
                   kappa_mn = log(0.5), 
                   kappa_sd = 1) {
  library(Matrix)
  library(MASS)
  library(spam)
  library(geoR)
  library(dbarts)
  library(splines2)
  
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
  
  
  # Propensity score estimation
  if(spatial_glm == "glm") {
    glm_fit <- glm(Tr ~ ., data = as.data.frame(X), family = "binomial")
    logit_ps <- predict(glm_fit, as.data.frame(X))
    ps <- 1 / (1 + exp(-logit_ps))
  } else if(spatial_glm == "bart") {
    bart_fit <- dbarts::bart(x.train = X, y.train = Tr, x.test = Z, ndpost = 10000L, nskip = 2000L, verbose = FALSE)
    ps_mat <- apply(bart_fit$yhat.train, 1, function(x){1/(1 + exp(-x))})
    ps <- colMeans(t(ps_mat))
  } else if(spatial_glm == "spatial") {
    glm_fit <- glm(Tr ~ ., data = as.data.frame(X), family = "binomial")
    n.samples <- 10000
    burn.in <- 0.2*n.samples
    spatial_ps <- spBayes::spGLM(formula = Tr ~ ., 
                                 family = "binomial",
                                 data = as.data.frame(cbind(Tr, X)), 
                                 coords = as.matrix(H %*% as.matrix(domain)), 
                                 knots = as.matrix(domain),
                                 starting = list("beta" = coef(glm_fit), "phi" = mean(c(1/(rho+0.05), 1/(rho-0.05))), "sigma.sq" = 0.5, "w" = rnorm(G)),
                                 tuning = list("beta" = rep(0.1, ncol(X)+1), "phi" = 0.1, "sigma.sq" = 0.1, "w" = rep(0.01^2, G)),
                                 priors = list("beta.Normal" = list(rep(0, ncol(X)+1), rep(10, ncol(X)+1)), "phi.Unif" = c(1/(rho+0.05), 1/(rho-0.05)), "sigma.sq.IG" = c(0.1, 0.1)),
                                 cov.model = "exponential",
                                 n.samples = n.samples,
                                 verbose = FALSE)
    intercept <- spatial_ps$p.beta.theta.samples[burn.in:n.samples, 1]
    Xbeta <- as.vector(X %*% colMeans(spatial_ps$p.beta.theta.samples[burn.in:n.samples, 2:3]))
    w <- rowMeans(spatial_ps$p.w.samples[,burn.in:n.samples])
    logit_ps <- intercept + Xbeta + w
    ps <- 1/(1 + exp(-logit_ps))
  }
  dens <- density(ps, from = min(ps), to = max(ps))
  cum_density <- cumsum(dens$y) / sum(dens$y)
  inv_cdf <- approxfun(cum_density, dens$x)
  probs <- seq(0, 1, length.out = df-1)[-c(1, df-1)]
  knots <- inv_cdf(probs)
  ps_bSp <- splines2::bSpline(ps, knots = knots)
  
  
  # covariates
  XA <- sweep(x = X, MARGIN = 1, STATS = Tr, FUN = "*")
  X_tot <- cbind(rep(1,n), Tr, X, ps_bSp, XA)
  
  
  # Initial value designation
  lin.mod <- lm(Y~X_tot-1)
  alpha0 <- as.vector(lin.mod$coefficients)[1]
  alpha1 <- as.vector(lin.mod$coefficients)[2]
  beta0 <- as.vector(lin.mod$coefficients)[3:(p+df+2)]
  beta1 <- as.vector(lin.mod$coefficients)[(p+df+3):ncol(X_tot)]
  reg_coef <- c(alpha0, alpha1, beta0, beta1)
  sig2y <- sum(lin.mod$residuals^2)/sum(N)
  
  
  # Precomputes Matern covariance with rho and kappa grids 
  nr <- length(rho_seq)
  kappa.u <- 0.5
  CorU.grid <- array(0, c(G, G, nr))
  InvCorU.grid <- array(0, c(G, G, nr))
  for(r in 1:nr){
    CorU.grid[,,r] <- corfx(distMat, rho_seq[r], kappa.u)
    InvCorU.grid[,,r] <- chol2inv(chol(CorU.grid[,,r]))
  }
  rho_u_ind <- ifelse(is.numeric(fix_rho), which(rho_seq == fix_rho), ceiling((1+nr)/2))
  rho.u <- rho_seq[rho_u_ind]
  InvCorU <- InvCorU.grid[,,rho_u_ind]
  sig2u <- 1
  u <- rnorm(G)
  
  
  # Keep track of stuff
  varnames <- c("alpha0", paste("beta0", c(cov.names, colnames(ps_bSp))), "alpha1", paste("beta1", cov.names), "rho.u", "sig2u", "kappa.u", "sig2y")
  keepers <- matrix(NA, iters, length(varnames))
  colnames(keepers) <- varnames
  
  ATE_vec <- rep(NA, iters)
  u_mn <- v_mn <- 0
  u_var <- v_var <- 0
  
  
  # RW Metropolis setup
  acc <- rep(0, 2)
  names(acc) <- c("rho.u", "kappa.u")
  att <- acc
  MH <- rep(0.1, 2)
  
  
  for(iter in 1:(burn+iters_thin)) {
    # alpha0 
    u.vec <- as.vector(H%*%u)
    Cov.y <- solve(t(X_tot)%*%X_tot/sig2y + diag(ncol(X_tot))/pri_sd_beta^2)
    mean.y <- t(X_tot)%*%(Y-u.vec)/sig2y
    reg_coef <- as.vector(rmvnorm(1, Cov.y%*%mean.y, Cov.y))
    Xb <- as.vector(X_tot%*%reg_coef)
    
    alpha0 <- as.vector(reg_coef)[1]
    alpha1 <- as.vector(reg_coef)[2]
    beta0 <- as.vector(reg_coef)[3:(p+df+2)]
    beta1 <- as.vector(reg_coef)[(p+df+3):ncol(X_tot)]
    
    # sig2y
    QF.y <- sum((Y-Xb-u.vec)^2)
    sig2y <- 1/rgamma(1, n/2+a, QF.y/2+b)
    
    
    # u
    mu_u <- as.vector(t(H)%*%(Y-Xb))/sig2y
    Qu <- diag(N/sig2y)
    QQ <- InvCorU/sig2u
    C <- chol2inv(chol(Qu+QQ))
    bb <- mu_u 
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
    
    
    # Step size tuning
    if(iter<burn){for(k in 1:length(MH)){if(att[k] > 50){
      if(acc[k]/att[k] < 0.3){MH[k] <- MH[k]*0.8}
      if(acc[k]/att[k] > 0.5){MH[k] <- MH[k]*1.2}
      acc[k] <- att[k] <- 0
    }}}
    
    
    # KEEP TRACK OF STUFF
    if(iter<burn) {
      keepers[iter,] <- c(alpha0, beta0, alpha1, beta1, rho.u, sig2u, kappa.u, sig2y)
      ATE_vec[iter] <- alpha1 + mean(Z%*%beta1)
    } else {
      if(iter%%thin == 0) {
        keepers[burn+(iter-burn)/thin,] <- c(alpha0, beta0, alpha1, beta1, rho.u, sig2u, kappa.u, sig2y)
        ATE_vec[burn+(iter-burn)/thin] <- alpha1 + mean(Z%*%beta1)
        u_mn <- u_mn + u/(iters-burn)
        u_var <- u_var + u^2/(iters-burn)
      }
    }
    
    if(isTRUE(verbose)) {
      if(iter%%update == 0) {
        cat(iter, "out of", burn+iters_thin, "number of iterations\n")
      }
    }
  }
  tock   <- proc.time()[3]
  output <- list(samps = keepers,
                 ATE = ATE_vec,
                 uv_mn = u_mn,
                 uv_var = u_var-u_mn^2,
                 acc_rate = acc/att,
                 time = (tock-tick)/60) # time is minute scale
  return(output)
}

ps_adj_gp <- function(Y,
                      Tr,
                      domain,
                      X,
                      Z,
                      H,
                      N0,
                      N1,
                      Leap = 20,
                      tau_L = 1/Leap,
                      pri_sd_beta = 10, 
                      a = 0.1, 
                      b = 0.1,
                      df = 5,
                      spatial_glm = c("glm", "bart", "spatial"),
                      euclidean = TRUE,
                      iters = 20000, 
                      burn = 5000, 
                      update = 2000, 
                      thin = 1,
                      verbose = FALSE, 
                      fix_rho = FALSE,
                      fix_kappa.u = TRUE,
                      rho_seq = seq(0.01, 0.2, by = 0.01), 
                      kappa_mn = log(0.5), 
                      kappa_sd = 1) {
  library(Matrix)
  library(MASS)
  library(spam)
  library(geoR)
  library(dbarts)
  library(splines2)
  
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
  
  # Potential outcome
  Y0 <- Y1 <- rep(NA, nrow(X))
  Y0[which(Tr == 0)] <- Y[which(Tr == 0)]
  Y1[which(Tr == 1)] <- Y[which(Tr == 1)]
  
  na.y0 <- which(is.na(Y0))
  na.y1 <- which(is.na(Y1))
  N <- N0 + N1
  
  
  # Propensity score estimation
  if(spatial_glm == "glm") {
    glm_fit <- glm(Tr ~ ., data = as.data.frame(X), family = "binomial")
    logit_ps <- predict(glm_fit, as.data.frame(X))
    ps <- 1 / (1 + exp(-logit_ps))
  } else if(spatial_glm == "bart") {
    bart_fit <- dbarts::bart(x.train = X, y.train = Tr, x.test = Z, ndpost = 10000L, nskip = 2000L, verbose = FALSE)
    ps_mat <- apply(bart_fit$yhat.train, 1, function(x){1/(1 + exp(-x))})
    ps <- colMeans(t(ps_mat))
  } else if(spatial_glm == "spatial") {
    glm_fit <- glm(Tr ~ ., data = as.data.frame(X), family = "binomial")
    n.samples <- 10000
    burn.in <- 0.2*n.samples
    spatial_ps <- spBayes::spGLM(formula = Tr ~ ., 
                                 family = "binomial",
                                 data = as.data.frame(cbind(Tr, X)), 
                                 coords = as.matrix(H %*% as.matrix(domain)), 
                                 knots = as.matrix(domain),
                                 starting = list("beta" = coef(glm_fit), "phi" = mean(c(1/(rho+0.05), 1/(rho-0.05))), "sigma.sq" = 0.5, "w" = rnorm(G)),
                                 tuning = list("beta" = rep(0.1, ncol(X)+1), "phi" = 0.1, "sigma.sq" = 0.1, "w" = rep(0.01^2, G)),
                                 priors = list("beta.Normal" = list(rep(0, ncol(X)+1), rep(10, ncol(X)+1)), "phi.Unif" = c(1/(rho+0.05), 1/(rho-0.05)), "sigma.sq.IG" = c(0.1, 0.1)),
                                 cov.model = "exponential",
                                 n.samples = n.samples,
                                 verbose = FALSE)
    intercept <- mean(spatial_ps$p.beta.theta.samples[burn.in:n.samples, 1])
    Xbeta <- as.vector(X %*% colMeans(spatial_ps$p.beta.theta.samples[burn.in:n.samples, 2:3]))
    w <- rowMeans(spatial_ps$p.w.samples[,burn.in:n.samples])
    logit_ps <- intercept + Xbeta + w
    ps <- 1/(1 + exp(-logit_ps))
  }
  #dens <- density(ps, from = min(ps), to = max(ps))
  #cum_density <- cumsum(dens$y) / sum(dens$y)
  #inv_cdf <- approxfun(cum_density, dens$x)
  #probs <- seq(0, 1, length.out = df-1)[-c(1, df-1)]
  #knots <- inv_cdf(probs)
  knots <- seq(from = min(ps), to = max(ps), length.out = df-1)[-c(1, df-1)]
  ps_bSp <- splines2::bSpline(ps, knots = knots)
  
  
  # covariates
  XA <- sweep(x = X, MARGIN = 1, STATS = Tr, FUN = "*")
  X_tot <- cbind(rep(1,n), Tr, X, ps_bSp, XA)
  
  
  # Initial value designation
  lin.mod <- lm(Y~X_tot-1)
  alpha0 <- as.vector(lin.mod$coefficients)[1]
  alpha1 <- as.vector(lin.mod$coefficients)[2] + alpha0
  beta0 <- as.vector(lin.mod$coefficients)[3:(p+2)]
  beta_bs <- as.vector(lin.mod$coefficients)[(p+3):(p+df+2)]
  beta1 <- as.vector(lin.mod$coefficients)[(p+df+3):ncol(X_tot)] + beta0
  reg_coef <- c(alpha0, alpha1, beta_bs, beta0, beta1)
  sig2y0 <- sig2y1 <- sum(lin.mod$residuals^2)/sum(N)
  
  
  # Precomputes Matern covariance with rho and kappa grids 
  nr <- length(rho_seq)
  kappa.u <- 0.5
  CorU.grid <- array(0, c(G, G, nr))
  InvCorU.grid <- array(0, c(G, G, nr))
  for(r in 1:nr){
    CorU.grid[,,r] <- corfx(distMat, rho_seq[r], kappa.u)
    InvCorU.grid[,,r] <- chol2inv(chol(CorU.grid[,,r]))
  }
  rho_u_ind <- ifelse(is.numeric(fix_rho), which(rho_seq == fix_rho), ceiling((1+nr)/2))
  rho.u <- rho_seq[rho_u_ind]
  InvCorU <- InvCorU.grid[,,rho_u_ind]
  gamma.u <- 0
  sig2u0 <- sig2u1 <- 1
  u0t <- u1t <- rep(0, G)
  u0 <- u0t
  u1 <- u1t + gamma.u*u0t
  
  
  # Keep track of stuff
  varnames <- c("alpha0", 
                "alpha1", 
                paste("beta0", cov.names), 
                paste("beta1", cov.names), 
                paste("beta Baiss", 1:df),
                "rho.u", 
                "sig2u0",
                "sig2u1",
                "gamma.u",
                "kappa.u", 
                "sig2y0",
                "sig2y1")
  keepers <- matrix(NA, iters, length(varnames))
  colnames(keepers) <- varnames
  
  ATE_vec <- rep(NA, iters)
  u0_mn <- u1_mn <- 0
  u0_var <- u1_var <- 0
  
  
  # RW Metropolis setup
  acc <- rep(0, 2)
  names(acc) <- c("rho.u", "kappa.u")
  att <- acc
  MH <- rep(0.1, 2)
  
  
  for(iter in 1:(burn+iters_thin)) {
    ############################################
    ## Bayesian imputation for missing values ##
    ############################################
    u0.vec <- as.vector(H%*%u0)
    u1.vec <- as.vector(H%*%u1)
    
    Y0[na.y0] <- rnorm(sum(N1), (X%*%beta0 + ps_bSp%*%beta_bs + u0.vec)[na.y0], sqrt(sig2y0)) + alpha0
    Y1[na.y1] <- rnorm(sum(N0), (X%*%beta1 + ps_bSp%*%beta_bs + u1.vec)[na.y1], sqrt(sig2y1)) + alpha1
    
     
    #########################################
    ## Parameters involving normal layer Y ##
    #########################################
    # alpha0 
    u0.vec <- as.vector(H%*%u0)
    Cov.y <- 1/(n/sig2y0 + 1/pri_sd_beta^2)
    mean.y <- sum(Y0 - u0.vec - X%*%beta0 - ps_bSp%*%beta_bs)/sig2y0
    alpha0 <- rnorm(1, Cov.y*mean.y, sqrt(Cov.y))
    
    
    # alpha1 
    u1.vec <- as.vector(H%*%u1)
    Cov.y <- 1/(n/sig2y1 + 1/pri_sd_beta^2)
    mean.y <- sum(Y1 - u1.vec - X%*%beta1 - ps_bSp%*%beta_bs)/sig2y1
    alpha1 <- rnorm(1, Cov.y*mean.y, sqrt(Cov.y))
    
    
    # beta_bs
    Qbeta <- solve(t(ps_bSp)%*%ps_bSp/sig2y0 + t(ps_bSp)%*%ps_bSp/sig2y1 + diag(df)/pri_sd_beta^2)
    bbeta <- t(ps_bSp)%*%(Y0 - alpha0 - u0.vec - X%*%beta0)/sig2y0 + t(ps_bSp)%*%(Y1 - alpha1 - u1.vec - X%*%beta1)/sig2y1
    beta_bs <- Qbeta%*%bbeta + t(chol(Qbeta))%*%rnorm(df)
    
    
    # beta0
    Qbeta <- solve(t(X)%*%X/sig2y0 + diag(p)/pri_sd_beta^2)
    bbeta <- t(X)%*%(Y0 - alpha0 - u0.vec - ps_bSp%*%beta_bs)/sig2y0
    beta0 <- Qbeta%*%bbeta + t(chol(Qbeta))%*%rnorm(p)
    
    
    # beta1
    Qbeta <- solve(t(X)%*%X/sig2y1 + diag(p)/pri_sd_beta^2)
    bbeta <- t(X)%*%(Y1 - alpha1 - u1.vec - ps_bSp%*%beta_bs)/sig2y1
    beta1 <- Qbeta%*%bbeta + t(chol(Qbeta))%*%rnorm(p)
    Xb0 <- as.vector(X%*%beta0 + ps_bSp%*%beta_bs) + alpha0
    Xb1 <- as.vector(X%*%beta1 + ps_bSp%*%beta_bs) + alpha1
    
    
    # sig2y0
    QF.y <- sum((Y0-Xb0-u0.vec)^2)
    sig2y0 <- 1/rgamma(1, n/2+a, QF.y/2+b)
    
    
    # sig2y1
    QF.y <- sum((Y1-Xb1-u1.vec)^2)
    sig2y1 <- 1/rgamma(1, n/2+a, QF.y/2+b)
    
    
    #############################################
    ## Latent spatial random effects U0 and U1 ##
    #############################################
    # u0.tilde
    u1t.vec <- as.vector(H%*%u1t)
    mu0u <- as.vector(t(H)%*%(Y0-Xb0))/sig2y0
    mu1u <- as.vector(t(H)%*%(Y1-Xb1-u1t.vec))*gamma.u/sig2y1
    Q0u <- diag(N/sig2y0)
    Q1u <- diag(N*gamma.u^2/sig2y1)
    QQ <- InvCorU/sig2u0
    C <- chol2inv(chol(Q0u+Q1u+QQ))
    bb <- mu0u + mu1u
    u0t <- C%*%bb + t(chol(C))%*%rnorm(G)
    
    
    # u1.tilde
    u0t.vec <- as.vector(H%*%u0t)
    mu1u <- as.vector(t(H)%*%(Y1-Xb1-gamma.u*u0t.vec))/sig2y1
    Q1u <- diag(N/sig2y1)
    QQ <- InvCorU/sig2u1
    C <- chol2inv(chol(Q1u+QQ))
    bb <- mu1u
    u1t <- C%*%bb + t(chol(C))%*%rnorm(G)
    
    
    ####################################
    ## Linear model of coreg. gamma u ##
    ####################################
    u0t.vec <- as.vector(H%*%u0t)
    u1t.vec <- as.vector(H%*%u1t)
    mu1u <- as.vector(t(H)%*%(Y1-Xb1-u1t.vec))
    var.pt <- sum(u0t.vec^2)/sig2y1 + 1/pri_sd_beta^2
    mean.pt <- sum(u0t.vec*(Y1-Xb1-u1t.vec))/sig2y1
    gamma.u <- rnorm(1, mean.pt/var.pt, sqrt(1/var.pt))
    u0 <- u0t
    u1 <- u1t + gamma.u*u0t
    
    
    #######################################
    ## Variance parameters for U0 and U1 ##
    #######################################
    QF.u <- as.numeric(t(u0t)%*%InvCorU%*%u0t)
    sig2u0 <- 1/rgamma(1, G/2 + a, QF.u/2 + b)
    
    QF.u <- as.numeric(t(u1t)%*%InvCorU%*%u1t)
    sig2u1 <- 1/rgamma(1, G/2 + a, QF.u/2 + b)
    
    
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
    
    
    # Step size tuning
    if(iter<burn){for(k in 1:length(MH)){if(att[k] > 50){
      if(acc[k]/att[k] < 0.3){MH[k] <- MH[k]*0.8}
      if(acc[k]/att[k] > 0.5){MH[k] <- MH[k]*1.2}
      acc[k] <- att[k] <- 0
    }}}
    
    
    # KEEP TRACK OF STUFF
    if(iter<burn) {
      keepers[iter,] <- c(alpha0, alpha1, beta0, beta1, beta_bs, rho.u, sig2u0, sig2u1, gamma.u, kappa.u, sig2y0, sig2y1)
      ATE_vec[iter] <- alpha1 - alpha0 + mean(Z%*%(beta1-beta0)) + mean(u1 - u0)
    } else {
      if(iter%%thin == 0) {
        keepers[burn+(iter-burn)/thin,] <- c(alpha0, alpha1, beta0, beta1, beta_bs, rho.u, sig2u0, sig2u1, gamma.u, kappa.u, sig2y0, sig2y1)
        ATE_vec[burn+(iter-burn)/thin] <- alpha1 - alpha0 + mean(Z%*%(beta1-beta0)) + mean(u1 - u0)
        u0_mn <- u0_mn + u0/(iters-burn)
        u1_mn <- u1_mn + u1/(iters-burn)
        u0_var <- u0_var + u0^2/(iters-burn)
        u1_var <- u1_var + u1^2/(iters-burn)
      }
    }
    
    if(isTRUE(verbose)) {
      if(iter%%update == 0) {
        cat(iter, "out of", burn+iters_thin, "number of iterations\n")
      }
    }
  }
  tock   <- proc.time()[3]
  output <- list(samps = keepers,
                 ATE = ATE_vec,
                 uv_mn = cbind(u0_mn, u1_mn),
                 uv_var = cbind(u0_var-u0_mn^2, u1_var-u1_mn^2),
                 acc_rate = acc/att,
                 time = (tock-tick)/60) # time is minute scale
  return(output)
}

runModel_matern_ps_adj <- function (nonGauss = FALSE, nonstat = FALSE, phi = 2/3, lambda = 5, 
                                    rho = 0.1, iters = 120000, burn = 50000, df = 5) 
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
  gamma.u <- -0.5
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
  
  fit <- list(ps_adj_glm = ps_adj_glm, 
              ps_adj_brt = ps_adj_brt, 
              True_ATE = true_ATE, 
              True_phi = phi, 
              True_rho = rho, 
              Mean_N0 = mean(N0), 
              Mean_N1 = mean(N1), 
              NS = nonstat, 
              NG = nonGauss)
  
  return(fit)
}

