test1 :: Bool
test1 = low == low

test2 :: Bool
test2 = simulate adder (low, ([low], [low])) == low
