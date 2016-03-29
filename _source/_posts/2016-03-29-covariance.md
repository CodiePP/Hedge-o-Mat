---
layout: post
title:  "Covariance"
date:   2016-03-29 22:44:01
categories: statistics
---

Measures the variance of two data series around their mean values.

$$ Covar(X,Y)=\frac{1}{N}\sum_i{(X_i-\bar{X})(Y_i-\bar{Y})} $$ 

where $$ \bar{X}=\frac{1}{N}*\sum_i{X_i} $$

The covariance can be computed incrementally:

$$ Covar(X)=\bar{X*Y} - (\bar{X}*\bar{Y}) $$

Thus, we sum all $$X_i$$, $$Y_i$$ and all products $$X_i*Y_i$$, then build the
difference of their mean values.

