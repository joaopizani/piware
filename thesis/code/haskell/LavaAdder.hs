adder :: (Signal Bool, ([Signal Bool], [Signal Bool]))
      -> ([Signal Bool], Signal Bool)

adder (carryIn, ([] ,[]))    = ([], carryIn)
adder (carryIn, (a:as, b:bs) = (sum:sums, carryOut)
    where (sum, carry)     = fullAdd (carryIn, (a, b))
          (sums, carryOut) = adder (carry, (as, bs))
