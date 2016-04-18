module Main where
import Haste
import Haste.DOM
import Haste.Events

import ProcNum

main = withElems ["pv","ty","r","result"] calculator

calculator [pv,ty,r,result] = do
    onEvent pv  KeyUp $ \_ -> recalculate
    onEvent ty  KeyUp $ \_ -> recalculate
    onEvent r Change $ \_ -> recalculate
  where
    recalculate = do
      vpv <- getValue pv
      vty <- getValue ty
      vr <- getValue r
      case (str2dbl vpv, str2dbl vty, str2dbl vr) of
        (Just pv', Just ty', Just r') -> setProp result "innerHTML" (prtdbl2 $ calc pv' ty' r')
        _                  -> return ()

    calc :: Double -> Double -> Double -> Double
    calc pv ty r = pv * (1.0 + r)**ty


