---
layout: post
title:  "Put-call parity"
date:   2016-03-29 22:44:01
categories: methods
---

For European calls and puts their prices are related by the Put-call parity:

$$ p + S_0e^{-qT} = c + Ke^{-rT} $$

where $$p$$ and $$c$$ are the prices of the put, call options and $$S$$ is the
current spot price of the underlying, $$K$$ the strike price, $$T$$ the time to
maturity. The interest rate is integrated with $$r$$ and $$q$$ denotes the
dividend yield on the stock.

