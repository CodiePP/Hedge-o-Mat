{-# LANGUAGE OverloadedStrings #-}

module FinMath where


-- error function
-- numerical algorithm found on wikipedia
erf :: Double -> Double
erf z = if z >= 0 then
    1.0 - tau else
    tau - 1.0
    where
      t = 1.0 / (1.0 + 0.5 * abs(z))
      t2 = t * t
      t3 = t2 * t
      t4 = t3 * t
      t5 = t4 * t
      t6 = t5 * t
      t7 = t6 * t
      t8 = t7 * t
      t9 = t8 * t
      tau = t * exp( -z * z - 1.26551223 + 1.00002368*t + 0.37409196*t2 +
         0.09678418*t3 - 0.18628806*t4 + 0.27886807*t5 - 1.13520398*t6 +
         1.48851587*t7 - 0.82215223*t8 + 0.17087277*t9)

erfc z = 1.0 - (erf z)


cndf :: Double -> Double -> Double -> Double
cndf x mu sigma = 
    0.5 * erfc((-z) * invsqrt2)
    where
      z = (x - mu) / sigma
      invsqrt2 = 1.0 / 1.4142135623730950488017


priceCall :: Double -> Double -> Double -> Double -> Double -> Double
priceCall s k r tau sigma =
    s * (cndf d1 0.0 1.0) - k*exp((-r)*tau) * (cndf d2 0.0 1.0)

    where
        m = k / s
        sigma2div2 = sigma*sigma / 2.0
        iFun = \m' s' inner r' t' ->  ((-(log m')) + t' * (r' + inner)) / s' / (sqrt t')
        d1 = iFun m sigma  sigma2div2 r tau
        d2 = iFun m sigma (-sigma2div2) r tau

pricePut :: Double -> Double -> Double -> Double -> Double -> Double
pricePut s k r tau sigma =
    k*exp((-r)*tau) * (cndf (-d2) 0.0 1.0) - s * (cndf (-d1) 0.0 1.0)

    where
        m = k / s
        sigma2div2 = sigma*sigma / 2.0
        iFun = \m' s' inner r' t' ->  ((-(log m')) + t' * (r' + inner)) / s' / (sqrt t')
        d1 = iFun m sigma  sigma2div2 r tau
        d2 = iFun m sigma (-sigma2div2) r tau

