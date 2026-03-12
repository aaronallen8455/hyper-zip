import HyperZip

-- Test case 1: Direct replicate (should fuse)
testFusion1 :: [Int]
testFusion1 = zipWithN
  (\x y z -> x + y + z :: Int)
  (replicate 1000000 1)
  (replicate 1000000 2)
  (replicate 1000000 3)

-- Test case 2: Pre-allocated lists (won't fuse)
list1, list2, list3 :: [Int]
list1 = replicate 1000000 1
list2 = replicate 1000000 2
list3 = replicate 1000000 3
{-# NOINLINE list1 #-}
{-# NOINLINE list2 #-}
{-# NOINLINE list3 #-}

testNoFusion :: [Int]
testNoFusion = zipWithN
  (\x y z -> x + y + z :: Int)
  list1
  list2
  list3

main :: IO ()
main = do
  putStrLn "Testing with fusion (should be fast):"
  print $ length testFusion1
  putStrLn "Testing without fusion (should be slower):"
  print $ length testNoFusion
