---
layout: post
title:  "Exotic options"
date:   2016-03-30 22:44:01
categories: instruments
---

see chapter 24 in [Hull, Options, Futures, and other Derivatives](../books/hull-options-futures-and-other-derivatives.html)

### Nonstandard American options
Standard American options can be exercised at any time up to their maturity.
Restricting exercise to certain dates (<strong>Bermudan options</strong>) or
disallowing during certain parts of the option's life cycle (<strong>lock out
periods</strong>) creates variations of American options. Such nonstandard
American options can be valued using binomial trees where at each node a test is
inserted whether early exercise is admitted and of value.
### Forward start options
Valuation: ...
### Compound options
These are options on options:

European call on a call:
$$
S_0e^{-qT_2}M(a_1,b_1;\sqrt{T_1/T_2})-K_2e^{-rT_2}M(a_2,b_2;\sqrt{T_1/T_2})-e^{-rT_1}K_1N(a2)
$$

where

$$ a_1 = \frac{ln(S_0/S^{*})+(r-q+\sigma^2/2)T_1}{\sigma\sqrt{T_1}}, a_2 = a_1 -
\sigma\sqrt{T_1} $$

$$ b_1 = \frac{ln(S_0/K_2)+(r-q+\sigma^2/2)T_2}{\sigma\sqrt{T_2}}, b_2 = b_1 -
\sigma\sqrt{T_2} $$

The function M(a,b; ρ) is a bivariate normal distribution found on J. Hull's
website in Technical Note #5. S<sup>*</sup> is the asset price at time
T<sub>1</sub> for which the option price is K<sub>1</sub>.

European put on a call:
$$ K_2e^{-rT_2}M(-a_2,b_2;-\sqrt{T_1/T_2}) -
S_0e^{-qT_2}M(-a_1,b_1;-\sqrt{T_1/T_2}) + e^{-rT_1}K_1N(-a2) $$

European call on a put:
$$ K_2e^{-rT_2}M(-a_2,-b_2;\sqrt{T_1/T_2}) -
S_0e^{-qT_2}M(-a_1,-b_1;\sqrt{T_1/T_2}) - e^{-rT_1}K_1N(-a2) $$

European put on a put:
$$ S_0e^{-qT_2}M(a_1,-b_1;-\sqrt{T_1/T_2}) -
K_2e^{-rT_2}M(a_2,-b_2;-\sqrt{T_1/T_2}) + e^{-rT_1}K_1N(a2) $$
<!--more-->
<h3>Chooser options</h3>
Such options can be switched to a put or a call after a certain time. Its value
at time T<sub>1</sub> is $$ max(c, p) $$. For European options call-put-parity
provides a valuation:
$$ max(c, p) = max(c, c+Ke^{-r(T_2-T_1)}-S_1e^{-q(T_2-T_1)})
= c + e^{-q(T_2-T_1)}max(0,Ke^{-(r-q)(T_2-T_1)}-S_1) $$
It is shown that this corresponds to a package of:
1.) A call option with strike K and maturity T<sub>2</sub>
2.) $$ e^{-q(T_2-T_1)} $$ put options with strike $$ Ke^{-(r-q)(T_2-T_1)} $$ and
maturity T<sub>1</sub>
<h3>Barrier options</h3>
Either <strong>knock-in</strong> option, which begins after a barrier has been
touched, or <strong>knock-out</strong> option, which ceases to exist after the
event.
Valuation: ...

<!--more-->
### Binary options
Such options provide discontinuous payoffs after an event has occurred.
<strong>Cash-or-nothing call</strong>: pays a fixed amount Q if it ends in the
money (ITM), thus at time T the spot price S<sub>T</sub> is above the strike
price K. Its value depends on the probability of ending in the money: $$
Qe^{-rT}N(d_2) $$.
<strong>Cash-or-nothing put</strong>: pays a fixed amount Q if it ends ITM, thus
below the strike: $$ Qe^{-rT}N(-d_2) $$.
<strong>Asset-or-nothing call</strong>: this pays the asset price if it ends
ITM, thus S<sub>T</sub> &gt; K, otherwise nothing. Its value is $$
S_0e^{-qT}N(d_1) $$.
<strong>Asset-or-nothing put</strong>: only pays the asset price if it ends ITM,
thus below the strike price. Its value is $$ S_0e^{-qT}N(-d_1) $$.

An European call options is a combination of LONG an asset-or-nothing call and
SHORT a cash-or-nothing call (Q = K). Similarly for the put option: LONG
cash-or-nothing put (Q = K) and SHORT asset-or-nothing put.
<h3>Lookback options</h3>
These options provide payoffs depending on the lows and highs of S<sub>t</sub>
during their lifetime.
<strong>Floating lookback call</strong>: pays the difference between
S<sub>T</sub> and the minimal observed asset price S<sub>min</sub>.
$$ c_{fl} = S_0e^{-qT}N(a_1) - S_0e^{-qT}\frac{\sigma^2}{2(r-q)}N(-a_1) -
S_{min}e^{-rT}[N(a_2) - \frac{\sigma^2}{2(r-q)}e^{Y_1}N(-a_3)] $$
where
$$ a_1 = \frac{ln(S_0/S_{min}) + (r-q+\sigma^2/2)T}{\sigma\sqrt{T}} $$
$$ a_2 = a_1 - \sigma\sqrt{T} $$
$$ a_3 = \frac{ln(S_0/S_{min}) + (-r+q+\sigma^2/2)T}{\sigma\sqrt{T}} $$
$$ Y_1 = - \frac{2(r-q-\sigma^2/2)ln(S_0/S_{min})}{\sigma^2} $$

<strong>Floating lookback put</strong>: pays the difference between the maximum
observed asset price S<sub>max</sub> and S<sub>T</sub>.
$$ p_{fl} = S_{max}e^{-rT}[N(b_1) - \frac{\sigma^2}{2(r-q)}e^{Y_2}N(-b_3)] +
S_0e^{-qT}\frac{\sigma^2}{2(r-q)}N(-b_2) - S_0e^{-qT}N(b_2) $$
where
$$ b_1 = \frac{ln(S_{max}/S_0) + (-r+q+\sigma^2/2)T}{\sigma\sqrt{T}} $$
$$ b_2 = b_1 - \sigma\sqrt{T} $$
$$ b_3 = \frac{ln(S_{max}/S_0) + (r-q-\sigma^2/2)T}{\sigma\sqrt{T}} $$
$$ Y_2 = \frac{2(r-q-\sigma^2/2)ln(S_{max}/S_0)}{\sigma^2} $$

<!--more-->
### Shout options
An European option with the one-time possibility to lock-in the current asset
price during the lifetime of the option. At maturity the payoff depends on the
maximum of S<sub>τ</sub> or S<sub>T</sub>.

Valuation is similar to an American option using a binomial tree. At every node
in the tree the option's value is the maximum of the value if the holder shouts
or not.
### Asian options
The payoff of these options depends on the average price of the underlying asset
during the lifetime of the option.

<strong>Average price call</strong>: max(0, S<sub>avg</sub>
<strong>Average price put</strong>: max(0, K - S<sub>avg</sub>)
Using such options which cost less than regular options, it can be guaranteed
that on average a certain price level over some time is realized.

<strong>Average strike call</strong>: max(0, S<sub>T</sub> - S<sub>avg</sub>)
<strong>Average strike put</strong>: max(0, S<sub>avg</sub> - S<sub>T</sub>)
These options can guarantee that the average price paid or received for an asset
in frequent trading is not higher or not lower than a fixed amount.

Valuation in case of geometric average using the <a title="Black-Scholes-Merton
formula" href="/2010/10/black-scholes-merton-formula/">Black-Scholes-Merton
formula</a> and the following parameters:
$$ \sigma_{BS} = \frac{\sigma}{\sqrt{3}} $$
$$ q_{BS} = \frac{1}{2} (r+q+\frac{\sigma^2}{6}) $$

Valuation in case of the more often found arithmetic average case fits a
lognormal distribution to the moments:
$$ M_1 = \frac{e^{(r-q)T}-1}{(r-q)T}S_0 $$
$$ M_2 = \frac{2e^{[2(r-q)+\sigma^2]T} S_0^2}{(r-q+\sigma^2)(2r-2q+\sigma^2)T^2}
+ \frac{2S_0^2}{(r-q)T^2} [ \frac{1}{2(r-q)+\sigma^2} -
  \frac{e^{(r-q)T}}{r-q+\sigma^2} ] $$

  It follows:
  $$ F_0 = M_1 $$
  $$ \sigma^2 = \frac{1}{T} ln(\frac{M_2}{M^2_1}) $$

  which can be input into Black's model:
  $$ c = e^{-rT}[F_0N(d_1) - KN(d_2)] $$
  $$ p = e^{-rT}[KN(-d_2) - F_0N(-d_1)] $$
  and
  $$ d_1 = \frac{ln(F_0/K) + \sigma^2T/2}{\sigma\sqrt{T}} $$
  $$ d_2 = d_1 - \sigma\sqrt{T} $$

  <!--more-->
  <h3>Options to exchange one asset for another</h3>
  Valuation: ...
  <h3>Options involving several assets</h3>
  Valuation: ...
  <h3>Volatility and variance swaps</h3>
  ...

