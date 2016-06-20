
module MyWarrant
       (PlainVanillaOption(..), value)
       where

import MyTypes
import FinMath (cndfz)

data PlainVanillaOption = PVO {
                       strike :: Price
                     , price :: Price
                     , rate :: Double
                     , tdiff :: Double
                     , volatility :: Double 
                     , ratio :: Double
                     , isput :: Bool }
            deriving (Show, Eq, Read)

value :: PlainVanillaOption -> [(String,Double)]
value o =
  let p = ( (pc * s * cndfz(pc * d1) ) - (pc * k * eRT * cndD2) ) * z in
  let delta = if isput o then
                cndfz(d1) - 1
              else
                cndfz(d1) in
  let theta = ((( (-s) * stdD1 * v) / 2 / sqrtT) - (pc * r * k * eRT * cndD2)) / 365 in
  let gamma = stdD1 / s / v / sqrtT in
  let vega = s * sqrtT * stdD1 in
  let rho = pc * k * t * eRT * cndD2 in
  zip ["price","delta","gamma","theta","vega","rho"]
       [p, delta, gamma, theta, vega, rho]
  where
    pc = if isput o then -1 else 1
    k = px $ (strike o)
    s = px $ (price o)
    r = rate o
    t = tdiff o
    sqrtT = sqrt t
    v = volatility o
    z = ratio o
    d1 = price_option_D1 k s r t v
    d2 = price_option_D2 d1 t v
    stdD1 = stdnormf d1
    cndD2 = cndfz(pc * d2)
    eRT = exp ((-r) * t)

price_option_D1 :: Double -> Double -> Double -> Double -> Double -> Double
price_option_D1 k s r t v = 
        (log(s/k) + ((r + ((v*v)/2.0))*t)) / v / sqrt t

price_option_D2 :: Double -> Double -> Double -> Double
price_option_D2 d1 t v =
        d1 - v * sqrt t

stdnormf :: Double -> Double
stdnormf v =
        exp(-(v*v)/2.0) / sqrt2Pi
        where
        sqrt2Pi = 2.506628274635072411139

