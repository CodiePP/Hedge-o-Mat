---
layout: post
title:  "Generalized Extreme Value distribution (GEV)"
date:   2016-03-28 22:44:01
categories: statistics
---

$$ gev(x) = exp(-(1+\frac{\xi(x-\mu)}{\sigma})^{\frac{-1}{\xi}}) $$

This distribution can be derived using the block maxima method: all observations x<sub>i</sub> are divided in equally spaced blocks. Then, we note the local maxima in each block. After normalization these maxima follow the GEV.

$$ \xi = 0 $$ : Gumbel distribution

$$ \xi < 0 $$ : Weibull distribution

$$ \xi > 0 $$ : Fréchet distribution

The Fréchet distribution shows significant **fat tails**.

