adderFun :: ProcFun (Int8 -> Int8 -> Int8)
adderFun = \$(newProcFun [d|
        adderFun' :: Int8 -> Int8 -> Int8
        adderFun' x y = x + y
    |])

adderProc :: Signal Int8 -> Signal Int8 -> Signal Int8
adderProc = zipWithSY "adderProcess" adderFun
