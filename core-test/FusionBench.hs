import HyperZip
import System.Environment

-- Should fuse - no intermediate lists (6 lists)
testFused :: Int -> Int
testFused n = sum $ zipWithN
  (\x1 x2 x3 x4 x5 x6 -> x1 + x2 + x3 + x4 + x5 + x6 :: Int)
  (replicate n 1)
  (replicate n 2)
  (replicate n 3)
  (replicate n 4)
  (replicate n 5)
  (replicate n 6)

-- Should not fuse - intermediate lists exist (6 lists)
lists :: Int -> ([Int], [Int], [Int], [Int], [Int], [Int])
lists n = (replicate n 1, replicate n 2, replicate n 3, 
           replicate n 4, replicate n 5, replicate n 6)
{-# NOINLINE lists #-}

testUnfused :: Int -> Int
testUnfused n = 
  let (l1, l2, l3, l4, l5, l6) = lists n
  in sum $ zipWithN (\x1 x2 x3 x4 x5 x6 -> x1 + x2 + x3 + x4 + x5 + x6 :: Int) 
                    l1 l2 l3 l4 l5 l6

main :: IO ()
main = do
  args <- getArgs
  let n = if null args then 10000000 else read (head args)
  putStrLn $ "Fused (6 lists): " ++ show (testFused n)
  putStrLn $ "Unfused (6 lists): " ++ show (testUnfused n)
