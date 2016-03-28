---
layout: post
title:  "Jarque-Bera test (JB)"
date:   2016-03-28 22:44:01
categories: statistics
---

Tests whether a distribution of a random variable follows the normal distribution. Thus, whether its third and fourth moments, the [skewness](skewness.html) and [kurtosis](kurtosis.html), are equal to the values of a normal distribution: skewness = 0, kurtosis = 3.

Using the error term ($$ \hat{u} $$) of an OLS regression one can estimate these two parameters:

Skewness: $$ b1 = \frac{E[u^3]}{(\sigma^2)^{3/2}} $$

Kurtosis: $$ b2 = \frac{E[u^4]}{(\sigma^2)^{2}} $$

Test statistics:

$$ W = T[\frac{b_1^2}{6} + \frac{(b_2 - 3)^2}{24}] $$

where T is the sample size.

This test statistics follows a Chi<sup>2</sup> distribution with two degrees of freedom &Chi;<sup>2</sup>(2).
