---
layout: post
title:  "Normal distribution"
date:   2016-03-27 22:44:01
categories: statistics
---

very commonly used distribution

$$mean=\mu$$

$$variance=\sigma^2$$

$$pdf(x)=\frac{1}{\sqrt{2\pi}\sigma}\mbox{ } e^{-\frac{(x-\mu)^2}{2\sigma^2}}$$

The variable $$X \sim N(\mu, \sigma^2)$$ is said to be normally distributed with
mean and variance as $$\mu$$ and $$\sigma^2$$.
All normally distributed variables can be compared to each other by
transformation to the standard normal distribution:
$$ Z = \frac{X - \mu}{\sigma} $$ where $$ Z \sim N(\mu, \sigma^2) $$
The number of standard deviations away from the mean translates to the
probability $$P(Z{>}z) = 5{\%}$$  when $$z=1.67$$ or $$P(Z{>}z) = 1{\%}$$ when $$z=2.3$$

![Normal probability distribution](/images/npdf.png)

Code to reproduce this plot in `octave`:

{% highlight octave linenos %}
p=normpdf([-3:0.2:3],0,1);
plot(p);
title("Normal distribution");
xt2=[0,8,16,24,32];
set(gca,'XTick',xt2);
set(gca,'XTicklabel',{'-3.2','-1.6','0','1.6','3.2'});
print('npdf.ps','-dpsc2');
# convert npdf.ps -trim -resize 70% npdf.png
{% endhighlight %}

