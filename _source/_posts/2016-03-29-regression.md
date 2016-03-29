---
layout: post
title:  "Regression"
date:   2016-03-29 22:44:01
categories: statistics
---

Regression measures the linear relation between two timeseries.

$$ Y=\alpha+\beta*X+\epsilon $$

$$\left[ \begin{array} {cccc} r_{11} \: r_{12} \ldots r_{1n} \\
r_{21} \: r_{22} \ldots r_{2n} \\ \vdots 
  \\ r_{k1} \: r_{k2} \ldots r_{kn} \end{array}\right]
= \left[ \begin{array}{c} \alpha_1 \\ \alpha_2 \\ \vdots \\ \alpha_n \end{array}
\right]^T + \left[ \begin{array}{c} \beta_1 \\ \beta_2 \\ \vdots \\ \beta_n
\end{array} \right]^T \left[ \begin{array}{cc} 1 \: r_{X1} \\ 1 \: r_{X2}
\\ \vdots \\ 1 \: r_{Xk} \end{array} \right]$$

In `Matlab`/`Octave`:

{% highlight octave %}
[alpha;beta]=[1, r_X]  \ r_kn;
residuals = r_kn - ([1,r_X]*[alpha;beta]);
sigma_res = std(residuals);
alpha_adj = alpha ./ sigma_res;
{% endhighlight %}

Some wordings:

$$ ESS = \sum_t{(\hat{y}_t - \bar{y})^2} $$ explained sum of squares

$$ RSS = \sum_t{\epsilon_t^2} $$ residual sum of squares

$$ TSS = \sum_t{(y_t - \bar{y})^2} $$ total sum of squares

$$ TSS = ESS + RSS $$

Goodness of fit (R<sup>2</sup>):

$$ R^2 = 1 - \frac{ESS}{TSS} $$

adjusted R<sup>2</sup> by loss of degree of freedom (k variables, T
observations):
$$ {R_{adj}}^2 = 1 - [ \frac{T - 1}{T - k} (1 - R^2) ] $$

