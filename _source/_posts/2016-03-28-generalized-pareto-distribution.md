---
layout: post
title:  "Generalized Pareto distribution (GPD)"
date:   2016-03-28 22:44:01
categories: statistics
---

$$ gpd(x) = 1 - (1+\frac{\xi X}{\beta})^{\frac{-1}{\xi}} $$

note its similarity to the [GEV](generalized-extreme-value-distribution.html)(generalized extreme value distribution).

with $$ \xi > 0 $$ this distribution also shows significant **fat tails**. $$ \beta $$ is a scaling factor.

This distribution was derived using the peaks-over-threshold method: the conditional probability of a loss above a defined threshold.
