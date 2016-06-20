
module MyTypes where

type Currency = String
data Price = Px {currency :: String, px :: Double}
           deriving (Show, Eq, Read)



