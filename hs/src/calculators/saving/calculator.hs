module Main where
import Haste
import Haste.DOM
import Haste.Events

import ProcNum

main = withElems ["x","y","r","result"] calculator

calculator [x,y,r,result] = do
    onEvent x  KeyUp $ \_ -> recalculate
    onEvent y  KeyUp $ \_ -> recalculate
    onEvent r Change $ \_ -> recalculate
  where
    recalculate = do
      vx <- getValue x
      vy <- getValue y
      vr <- getValue r
      case (str2dbl vx, str2dbl vy, str2dbl vr) of
        (Just x', Just y', Just r') -> setProp result "innerHTML" (prtdbl2 $ calc x' y' r')
        _                  -> return ()

    calc :: Double -> Double -> Double -> Double
    calc x y r = log(x / y) / log(1.0 + r)


