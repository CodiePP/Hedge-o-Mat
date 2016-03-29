---
layout: post
title:  "Numerical date conversion in Matlab/Octave"
date:   2016-03-29 22:44:01
categories: methods
---

`datenum()` is very slow in Matlab, so I tried to write my own function which is
much faster:

{% highlight octave %}
function dtnum = date2num(sdt0)
% Matlab/Octave: fast numeric conversion 
% of string from format 'yyyy-mm-dd' to numerical date
  sdt = sdt0 - ['0'];
  y = sdt(1) * 1000 + sdt(2) * 100 + sdt(3) * 10 + sdt(4);
  m = sdt(6) * 10 + sdt(7);
  d = sdt(9) * 10 + sdt(10);
  dtnum = datenum(y,m,d);
end
{% endhighlight %}

in Octave on my laptop computer it only took 2.3 seconds to convert a date a
thouthand times with `date2num()`. The original function datenum() took
over 72 seconds. Thus, we have achieved a 31x speed improvement!

