---
layout: post
title:  "Durbin-Watson test"
date:   2016-03-28 22:44:01
categories: statistics
---

Tests for first order `autocorrelation`, i.e. between the value $$u_t$$ and the previous value $$u_{t-1}$$.

$$ DW = \frac{ \Sigma_{t=2}^{T} (\hat{u}_t - \hat{u}_{t-1})^2} {\Sigma_{t=2}^{T} \hat{u}_t^2} $$

The DW test can take values between 0 and 4.

  **0**: positive autocorrelation

  **2**: no autocorrelation

  **4**: negative autocorrelation

So values near 2 indicate that the series does not exhibit autocorrelation.

