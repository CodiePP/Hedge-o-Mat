---
layout: post
title:  "Probability"
date:   2016-03-29 22:44:01
categories: statistics
---

From the observation of a number of events $$X_i$$ of the same type, we can
conclude that such an event may occur with probability 

$$P(X) = \frac{1}{N}\sum_i X_i$$.

A population of random events can be modeled using the [normal
distribution](normal-distribution.html):

$$ X_i = N(\mu, { }\sigma^2) $$

The number follows the distribution with mean μ and standard deviation σ
(σ<sup>2</sup> is the variance).

If we have previously derived this distribution for a type of random variable,
we can evaluate the fit of every next instance of the variable to the
distribution:

$$ Z_i = \frac{X_i - \mu}{\sigma^2} $$

The Z-value measures how many standard deviations the value X<sub>i</sub>
deviates from the mean. The larger the Z-value the less likely does the value
X<sub>i</sub> follow this normal distribution, thus $$ X_i \sim N(\mu, {
  }\sigma^2) $$.

TODO: include `calculator`.
