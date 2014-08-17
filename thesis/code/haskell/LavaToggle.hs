toggle :: Signal Bool
toggle = let output = inv (latch output) in output
