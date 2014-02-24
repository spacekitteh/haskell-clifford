import Clifford

decay = map magnitude $ map head $ iterate (\init -> rk4ClassicalList init 0.001 (\x -> map negate x)) [1.0 `e` []]
