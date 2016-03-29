---
layout: post
title:  "Principle Component analysis (PCA)"
date:   2016-03-29 22:44:01
categories: statistics
---

This technique is used in situations where we want to reduce the dimensionality
of the data to be analysed. By definition a PCA transforms the input variables
(might be highly multicollinear) into independent linear combinations that are
`orthogonal`.
We can restate the problem as a search for `eigenvalues`/`eigenvectors`:

$$ \Lambda = \Gamma^T \Sigma \Gamma $$

where $$\Lambda$$ is the diagonal matrix of the eigenvalues and $$\Gamma$$ is a
matrix of eigenvectors (same dimensionality as input vars)

$$ Y = \Gamma^T X $$

The ratio $$ \Phi_i = \frac{\lambda_i}{\sum_k \lambda_k} $$ indicates the
proportion of total variation explained by one eigenvector (i).

The eigenvectors with the highest eigenvalues are chosen such that a desired
propotion of total variance of the sample is explained by them.

In Matlab/Octave:
{% highlight octave %}
% transform input matrix: mat
[nrows, ncols] = size(mat);
sumCols = sum(mat);
adjm = nan(nrows,ncols);
for j=1:ncols
  adjm(:,j) = mat(:,j) - (sumCols(j) / nrows);
end

% covariance matrix
covm = cov(adjm);
[eivec, eival] = eig(covm);
eival = diag(eival); % extract diagonal elements => eigenvalues

[seival si] = sort(eival, 'descend'); % sort descending, highest first

seivec = eivec(:,si); % sorted eigenvectors

% explanatory power of first eigenvalue/eigenvector
tev=seival ./ sum(seival);
fprintf(1, 'first eigenvector explains %.0f%% of total variance.\n',
tev(1)*100);
{% endhighlight %}

