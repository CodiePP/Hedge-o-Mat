{-# LANGUAGE OverloadedStrings #-}

module ProcNum where


str2dbl :: Maybe String -> Maybe Double
str2dbl Nothing = Nothing
str2dbl (Just v) = Just d
    where
      d = case (last v) of
            '%' -> (read $ init v :: Double) / 100.0
            _   -> read v :: Double


prtperc :: Double -> String
prtperc d = prtdbl 2 (d*100.0) ++ "%"

prtdbl2 :: Double -> String
prtdbl2 d = prtdbl 2 d
prtdbl3 :: Double -> String
prtdbl3 d = prtdbl 3 d
prtdbl4 :: Double -> String
prtdbl4 d = prtdbl 4 d

prtdbl :: Int -> Double -> String
prtdbl n d = 
    pre ++ "." ++ (take n post)
    where 
      p = 10**(fromIntegral n)
      d' = (fromIntegral $ round(d * p)) / p
      (pre,post) = splitdot $ show d'

splitdot :: String -> (String, String)
splitdot s = splitdota' s ([],[])

splitdota' [] (as',bs') = (reverse as', reverse bs')
splitdota' ('.':r) (as',bs') = splitdotb' r (as', [])
splitdota' (a:r) (as',bs') = splitdota' r (a:as',bs')
splitdotb' [] (as,bs) = (reverse as, reverse bs)
splitdotb' (b:r) (as,bs) = splitdotb' r (as,b:bs)

