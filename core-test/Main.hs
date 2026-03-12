import           HyperZip

test :: [Int]
test =
  -- zipWithN
    -- (\x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 :: Int)
    -- (replicate 100 1)
    -- (replicate 100 2)
    -- (replicate 100 3)
    -- (replicate 100 4)
    -- (replicate 100 5)
    -- (replicate 100 6)
    -- (replicate 100 7)
    -- (replicate 100 8)
    -- (replicate 100 9)
    -- (replicate 100 10)
    -- (replicate 100 11)
    -- (replicate 100 12)
    -- (replicate 100 13)
    -- (replicate 100 14)
  zipWithN
    (\x1 x2 x3 x4 x5 -> x1 + x2 + x3 + x4 + x5 :: Int)
    (replicate 100 1)
    (replicate 100 2)
    (replicate 100 3)
    (replicate 100 4)
    (replicate 100 5)

main :: IO ()
main = print (length test, head test, last test)
