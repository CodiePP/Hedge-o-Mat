---
layout: post
title:  "Coherent risk measure"
date:   2016-03-28 22:44:01
categories: statistics
---

A coherent risk measure satifies the following features:

* sub-additivity: ρ(R<sub>1</sub> + R<sub>2</sub>) ≤ ρ(R<sub>1</sub>) + ρ(R<sub>2</sub>)
* monotonicity: ρ(R<sub>1</sub>) ≥ ρ(R<sub>2</sub>) if R<sub>1</sub> ≥ R<sub>2</sub>
* positive homogeneity: βρ(R) = ρ(βR), for all β&gt;0.
* translation invariant: ρ(R) + c = ρ(c + R) for all constants c.

Beware! the [VAR](../methods/VAR) measure violates the first feature (sub-additivity).
