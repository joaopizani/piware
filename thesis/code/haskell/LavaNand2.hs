nand2 :: (Signal Bool, Signal Bool) -> Signal Bool
nand2 (a, b) = inv (and2 (a, b))
