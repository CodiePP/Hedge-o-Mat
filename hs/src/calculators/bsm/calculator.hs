module Main where
import Haste
import Haste.DOM
import Haste.Events

import ProcNum
import FinMath

main = withElems ["s","k","r","t","sigma","resultC","resultP"] calculator

calculator [s,k,r,t,sigma,resultC,resultP] = do
    onEvent s  KeyUp $ \_ -> recalculate
    onEvent k  KeyUp $ \_ -> recalculate
    onEvent r Change $ \_ -> recalculate
    onEvent t Change $ \_ -> recalculate
    onEvent sigma Change $ \_ -> recalculate
    where
    recalculate = do
      vs <- getValue s
      vk <- getValue k
      vr <- getValue r
      vt <- getValue t
      vsigma <- getValue sigma
      case (str2dbl vs, str2dbl vk, str2dbl vr, str2dbl vt, str2dbl vsigma) of
        (Just s', Just k', Just r', Just t', Just sigma') -> do
            setProp resultC "innerHTML" (prtdbl2 $ priceCall s' k' r' t' sigma')
            setProp resultP "innerHTML" (prtdbl2 $ pricePut s' k' r' t' sigma')
        _                  -> return ()

