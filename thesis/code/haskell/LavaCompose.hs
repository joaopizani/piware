compose [] inp = inp
compose (circ : circs) = out
    where x   = circ inp
          out = compose circs x
