---
layout: post
title:  "Linear regression diagnostics"
date:   2016-03-29 22:44:01
categories: statistics
---

Linear regression is based on five assumptions:
1. $$ E(\epsilon_t) = 0 $$
2. $$ var(\epsilon_t) = \sigma^2 < \infty $$
3. $$ cov(\epsilon_i, \epsilon_j) = 0 $$
4. $$ cov(\epsilon_t, x_t) = 0 $$
5. $$ \epsilon_t \backsim N(0, \sigma^2) $$

The first assumption $$ E(\epsilon_t) = 0 $$ states that the mean of the
residuals, or the error term, is zero. This is always the case if a constant
term (as a variable) is included in the regression.

The second assumption $$ var(\epsilon_t) = \sigma^2 < \infty $$ states that
the variance must be constant, thus equal to &sigma;<sup>2</sup>. Such a
variance is called homoscedastic. If variance changes over time, or depending on
one variable, it is said to be heteroscedastic and the method of Ordinary Least
Squares (OLS) may not be applicable anymore. 
We describe two test to determine `homoscedasticity`:
[Goldfield-Quandt test](goldfield-quandt-test.html) and [White's
test](white-test.html).

The third assumption $$ cov(\epsilon_i, \epsilon_j) = 0 $$ ensures that error
terms are unrelated to each other, thus not serially correlated nor
autocorrelated.
A good test for autocorrelation is the [Durbin-Watson test](durbin-watson-test.html).

The fourth assumption $$ cov(\epsilon_t, x_t) = 0 $$ ensures that the
explanatory variables are not correlated with the error term. Otherwise the OLS
estimator is not consistent. Test: ?

The fifth assumption $$ \epsilon_t \backsim N(0, \sigma^2) $$ is the basis for
hypothesis testing. To test whether the error term follows a normal distribution
we use the [Jarque-Bera test](jarque-bera-test.html).





