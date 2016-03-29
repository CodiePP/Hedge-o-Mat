---
layout: post
title:  "Cash flow at risk (CFAR)"
date:   2016-03-29 22:44:01
categories: methods
---

Companies that are part of the "real" economy can barely assess their risk of
business activities with the [VAR](var.html) approach. They would rather want to know the
shortfall of their expected cash flows.

$$ CVAR = \alpha  \sigma_{CF} $$

Example: we expect cash flows of $10m over the next year, their volatility is
$3m.

$$ CVAR_{5%} = 1.65 * $3m = $4.95m $$

Thus, there is a 5% chance that cash flows fall below $5.05m (10-4.95) in the
next year.

Assumptions:
<ul>
<li>cash flows are normally distributed</li>
<li>we know their volatility</li>
<li>this volatility is constant for the period in question</li>
</ul>
