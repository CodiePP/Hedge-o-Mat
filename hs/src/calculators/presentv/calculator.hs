module Main where
import Haste
import Haste.DOM
import Haste.Events

import ProcNum

main = withElems ["fv","ty","r","result"] calculator

calculator [fv,ty,r,result] = do
    onEvent fv  KeyUp $ \_ -> recalculate
    onEvent ty  KeyUp $ \_ -> recalculate
    onEvent r Change $ \_ -> recalculate
  where
    recalculate = do
      vfv <- getValue fv
      vty <- getValue ty
      vr <- getValue r
      case (str2dbl vfv, str2dbl vty, str2dbl vr) of
        (Just fv', Just ty', Just r') -> setProp result "innerHTML" (prtdbl2 $ calc fv' ty' r')
        _                  -> return ()

    calc :: Double -> Double -> Double -> Double
    calc fv ty r = fv / (1.0 + r)**ty


