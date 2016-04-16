---
layout: post
title:  "Black-Scholes-Merton formula"
date:   2016-03-29 22:44:01
categories: methods
---

This formula was developped independently by Black and Scholes, and by Merton in
1980/81.
They received the Nobel prize for this "discovery" of such an important formula
to prize [options](../instruments/options.html) as financial instruments.

The formula depends on:

- *S*: the spot price of the underlying asset

- *K*: the strike price to buy/sell at maturity date

- *T*: the time to maturity (in years)

- *r*: the interest rate (now till maturity)

- *q*: the dividend yield

- *&sigma;*: the volatility of the underlying (or implied volatility)

We first calculate two terms that are subsequently used in simplified formulas:

$$ d_1=\frac{log(S/K) + (r -q +\frac{1}{2}\sigma^2)T}{\sigma\sqrt{T}} $$

$$ d_2=\frac{log(S/K) + (r -q -\frac{1}{2}\sigma^2)T}{\sigma\sqrt{T}} $$

**Value** $$ V=Se^{-qT}N(d_1) - Ke^{-rT}N(d_2) $$

**Delta**: $$ \frac{\partial V}{\partial S} = e^{-qT}N(d_1) $$

