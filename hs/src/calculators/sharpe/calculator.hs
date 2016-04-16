module Main where
import Haste
import Haste.DOM
import Haste.Events

import ProcNum

main = withElems ["rp","sp","rf","result"] calculator

calculator [rp,sp,rf,result] = do
    onEvent rp  KeyUp $ \_ -> recalculate
    onEvent sp  KeyUp $ \_ -> recalculate
    onEvent rf Change $ \_ -> recalculate
  where
    recalculate = do
      vrp <- getValue rp
      vsp <- getValue sp
      vrf <- getValue rf
      case (str2dbl vrp, str2dbl vsp, str2dbl vrf) of
        (Just rp', Just sp', Just rf') -> setProp result "innerHTML" (prtdbl2 $ calc rp' rf' sp')
        _                  -> return ()

    calc :: Double -> Double -> Double -> Double
    calc rp rf sp = (rp - rf) / sp


