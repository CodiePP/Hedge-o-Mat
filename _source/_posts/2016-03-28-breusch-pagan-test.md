---
layout: post
title:  "Breusch-Pagan test"
date:   2016-03-28 22:44:01
categories: statistics
---

This test is used in linear regressions to test for `homoscedasticity` of the error term. 

For the regression $$ Y = \beta X + u $$ verify homoscedastic $$ u_t $$ using the Breusch-Pagan test.

Regress the squared $$ u_t $$ back to the X:

$$ \hat{u_t}^2 =  \beta X + v $$ 

and calculate the test statistics: $$ nR^2 $$.

This test statistics is &Chi;<sup>2</sup> with (k-1) d.f. distributed under the null hypothesis of homoscedasticity.

