{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Zhype
  (
  ) where

import           Data.Kind
import           Control.Monad.Hyper

-- Use function type as the arg rather than type lists?
type ProducerTF :: [Type] -> Type -> Type
type family ProducerTF args fun where
  ProducerTF args (x -> y -> fun) =
    Hyper
      (BaseFunTF (x ': args) (ProducerTF (x ': args) (y -> fun)))
      (ProducerTF (x ': args) (y -> fun))
  ProducerTF args (v -> ResultTy res) = Hyper (BaseFunTF args [res]) [res]
  -- TODO: error case

type BaseFunTF :: [Type] -> Type -> Type
type family BaseFunTF args rest where
  BaseFunTF (x ': args) rest = BaseFunTF args (x -> rest)
  BaseFunTF '[] done = done

-- class ZipWithHyp a where
--   zipWithHyp :: ZipWithHypTyTF a

-- separate class to build the producer

-- buildProducer :: (x -> fun) -> ProducerTF (x ': args) fun -> [x] -> ProducerTF args fun
-- consumer :: fun -> ProducerTF args  -> [x] -> [ResultTF vars]

-- class ConstProducer '[] funTy => InitProducer funTy where
initProducer ::
  forall funTy firstArg funRest.
  ( ConstProducer '[] funTy
  , (firstArg -> funRest) ~ funTy
  , ProducerTF '[] funTy ~
      Hyper
        (BaseFunTF '[firstArg] (ProducerTF '[firstArg] (firstArg -> funRest)))
        (ProducerTF '[firstArg] (firstArg -> funRest))
  )
  => [firstArg] -> ProducerTF '[] funTy
initProducer =
  foldr
    (\x -> push ($ x))
    (constProducer @'[] @funTy)

class ConstProducer args funTy where
  constProducer :: ProducerTF args funTy

instance
  ProducerTF args (a -> ResultTy res) ~ Hyper (BaseFunTF args [res]) [res]
  => ConstProducer args (a -> ResultTy res) where
  constProducer = k []

instance
  ( ConstProducer (a ': args) (b -> c)
  , ProducerTF args (a -> b -> c) ~
      Hyper
        (BaseFunTF (a ': args) (ProducerTF (a ': args) (b -> c)))
        (ProducerTF (a ': args) (b -> c))
  )
  => ConstProducer args (a -> b -> c) where
  constProducer = k (constProducer @(a ': args) @(b -> c))

k :: a -> Hyper b a
k = pure

type FirstArgTF :: Type -> Type
type family FirstArgTF funTy where
  FirstArgTF (x -> rest) = x
  -- TODO: error case

-- Problem: how to identify the terminating instance for AppendProducer?
-- Could always just add a Nat param to induct on.
-- Another possibility is to attach a terminating signifier on the end of
-- the funTy. This could be a newtype wrapper that is internal.

newtype ResultTy a = ResultTy a

type MarkResultTF :: Type -> Type
type family MarkResultTF funTy where
  MarkResultTF (a -> b) = a -> MarkResultTF b
  MarkResultTF a = ResultTy a

-- appendProducer :: [a] -> ProducerTF args (a -> funTy) -> ProducerTF (a ': args) funTy

-- class AppendProducer a args funTy where

-- class FlippedConstProducer args funTy where
--   flippedConstProducer :: FlipHyperTF (ProducerTF args funTy)
--
-- instance
--   (FlipHyperTF (ProducerTF args (a -> b -> c))
--     ~ Hyper
--         (ProducerTF (a ': args) (b -> c))
--         (BaseFunTF (a ': args) (ProducerTF (a ': args) (b -> c)))
--   )
--   => FlippedConstProducer args (a -> b -> c) where
--   flippedConstProducer = k []

class ConstBaseFunc baseFunArgs args fun where
  constArgHyp :: BaseFunTF baseFunArgs (ProducerTF args fun)

instance ConstProducer args fun => ConstBaseFunc '[] args fun where
  constArgHyp = constProducer @args @fun

instance
  ( ConstBaseFunc baseFunArgs args fun
  , BaseFunTF (a ': baseFunArgs) (ProducerTF args fun)
      ~ (a -> BaseFunTF baseFunArgs (ProducerTF args fun))
  )
  => ConstBaseFunc (a ': baseFunArgs) args fun where
  constArgHyp = const (constArgHyp @baseFunArgs @args @fun)

-- type family ZipWithHypTyTF args res where
--   ZipWithHypTyTF '[] res = [res]
--   ZipWithHypTyTF (x ': xs) res = x -> ZipWithHypTyTF xs res

pushProducer
  :: forall args funTy a.
    ( ConstBaseFunc (a ': args) (a ': args) funTy
    , ProducerTF args (a -> funTy) ~
        Hyper
          (BaseFunTF (a ': args) (ProducerTF (a ': args) funTy))
          (ProducerTF (a : args) funTy)
    )
  => [a] -> ProducerTF args (a -> funTy) -> ProducerTF (a ': args) funTy
pushProducer as p = invoke p $
  foldr
    (pushProducerFold @args @funTy)
    (k (constArgHyp @(a ': args) @(a ': args) @funTy))
    as

pushProducerFold
  :: forall args funTy a.
      a -> Hyper
             (ProducerTF (a : args) funTy)
             (BaseFunTF args (a -> ProducerTF (a : args) funTy))
        -> Hyper
             (ProducerTF (a : args) funTy)
             (BaseFunTF args (a -> ProducerTF (a : args) funTy))
pushProducerFold = undefined

pushProducerFold'
  :: forall a b c d.
    b -> Hyper
            (ProducerTF '[a] (b -> c -> d))
            (BaseFunTF '[] (a -> ProducerTF '[a] (b -> c -> d)))
       -> Hyper
            (ProducerTF '[a] (b -> c -> d))
            (BaseFunTF '[] (a -> ProducerTF '[a] (b -> c -> d)))
pushProducerFold' =
  push .
    g
    . flip
      (id
    . flip . flip id)
  where
  g :: PartATF '[b,a] (c -> d)
      -- BaseFunTF '[a]
      --     ( BaseFunTF '[b, a] (ProducerTF '[b, a] (c -> d))
      --     -> ProducerTF '[b, a] (c -> d)
      --     )
      -- -> ProducerTF '[a] (b -> c -> d)
      -- -> BaseFunTF '[a]
      --     (ProducerTF '[a] (b -> c -> d))
  g = flip . (push .)

pushProducerFold''
  :: forall a x b c d.
    b -> Hyper
            (ProducerTF '[a,x] (b -> c -> d))
            (BaseFunTF '[x] (a -> ProducerTF '[a,x] (b -> c -> d)))
       -> Hyper
            (ProducerTF '[a,x] (b -> c -> d))
            (BaseFunTF '[x] (a -> ProducerTF '[a,x] (b -> c -> d)))
pushProducerFold'' =
  push .
    g
    . flip
      (flip . ((id . flip) .)
    . flip . flip id)
  where
   -- g :: --BaseFunTF [a,x] (ProducerTF [a,x] (b -> c -> d))
   --    BaseFunTF [a,x] (BaseFunTF [b,a,x] (ProducerTF '[b,a,x] (c -> d)) -> (ProducerTF '[b,a,x] (c -> d)))
   --    -> x -> ProducerTF '[a,x] (b -> c -> d)
   --    -> a -> ProducerTF '[a,x] (b -> c -> d)
   g = -- ((flip . (push .)) .)
       flip . ((flip . (push .)) .)

pushProducerFold'''
  :: forall a x b c d y.
    b -> Hyper
            (ProducerTF '[a,x,y] (b -> c -> d))
            (BaseFunTF '[x,y] (a -> ProducerTF '[a,x,y] (b -> c -> d)))
       -> Hyper
            (ProducerTF '[a,x,y] (b -> c -> d))
            (BaseFunTF '[x,y] (a -> ProducerTF '[a,x,y] (b -> c -> d)))
pushProducerFold''' =
  push .
    g
    . flip
      (flip . ((flip . (flip .) . flip) .)
    . flip . flip id)
  where
   g :: (y -> x -> a -> a4 -> b1)
                      -> Hyper a4 b1 -> y -> x -> a -> Hyper a4 b1
   g = flip . ((flip . ((flip . (push .)) .)) .)

type family PartATF args funTy where
  PartATF (a ': args) funTy =
    BaseFunTF args
         ( BaseFunTF (a ': args) (ProducerTF (a ': args) funTy)
          -> ProducerTF (a ': args) funTy
          )
    -> ProducerTF args (a -> funTy)
    -> BaseFunTF args (ProducerTF args (a -> funTy))

class FoldComponents args funTy where
  partA :: PartATF args funTy
--   partB :: _

instance ProducerTF '[] (x -> funTy) ~ Hyper (x -> ProducerTF '[x] funTy) (ProducerTF '[x] funTy)
  => FoldComponents '[x] funTy where
  partA = push

instance
    (ProducerTF '[y] (x -> funTy)
      ~ Hyper (y -> x -> ProducerTF [x, y] funTy) (ProducerTF [x, y] funTy)
    , FoldComponents '[] (y -> x -> funTy)
      )
  => FoldComponents '[x,y] funTy where
  partA = flip . (partA @'[] @(y -> x -> funTy) .)

-- instance FoldComponents (y ': args) (x -> funTy) => FoldComponents (x ': y ': args) funTy where
--   partA =  flip . ((partA @(y ': args) @(x -> funTy)) .)

  -- push . flip .
  --   ((flip . (push .)) .)
  --   . flip
  --     (flip . ((id . flip) .)
  --   . flip . flip id)

  -- push . flip .
  --   (push .)
  --   . flip
  --     (flip . flip id)


-- How to build 1st foldr arg
-- (cons . flip .
--   ((flip . partA) .)
--   . flip
--     (flip . ((partB . flip) .)
--   . flip . flip id))
--
-- partA base
-- (cons .)
-- partB base
-- id
--



-- zippWith5 :: forall a b c d e f. (a -> b -> c -> d -> e -> f) -> [a] -> [b] -> [c] -> [d] -> [e] -> [f]
-- zippWith5 f as bs cs ds es =
--   let p1 :: (a -> (a -> b -> (a -> b -> c -> (a -> b -> c -> d -> [f]) -=> [f])
--                      -=> ((a -> b -> c -> d -> [f]) -=> [f]))
--                  -=> ((a -> b -> c -> (a -> b -> c -> d -> [f]) -=> [f])
--                       -=> ((a -> b -> c -> d -> [f]) -=> [f])))
--              -=> ((a -> b -> (a -> b -> c -> (a -> b -> c -> d -> [f]) -=> [f])
--                       -=> ((a -> b -> c -> d -> [f]) -=> [f]))
--                   -=> ((a -> b -> c -> (a -> b -> c -> d -> [f]) -=> [f])
--                        -=> ((a -> b -> c -> d -> [f]) -=> [f])))
--       p1 = foldr
--             (\a -> cons ($ a))
--             (k (k (k (k []))))
--             as
--       p2 :: (a -> b -> (a -> b -> c -> (a -> b -> c -> d -> [f]) -=> [f])
--                -=> ((a -> b -> c -> d -> [f]) -=> [f]))
--            -=> ((a -> b -> c -> (a -> b -> c -> d -> [f]) -=> [f])
--                 -=> ((a -> b -> c -> d -> [f]) -=> [f]))
--       p2 = runHF p1 $
--            foldr
--             (\b -> cons (\acc a -> cons (\g -> g a b) acc))
--             (k (const (k (k (k [])))))
--             bs
--       p3 :: (a -> b -> c -> (a -> b -> c -> d -> [f]) -=> [f])
--            -=> ((a -> b -> c -> d -> [f]) -=> [f])
--       p3 = runHF p2 $
--            foldr
--             (\c -> cons (\acc a b -> cons (\g -> g a b c) acc))
--             (k (const (const (k (k [])))))
--             cs
--       p4 :: (a -> b -> c -> d -> [f]) -=> [f]
--       p4 = runHF p3 $
--            foldr
--             (\d -> cons (\acc a b c -> cons (\g -> g a b c d) acc))
--             (k (const (const (const (k [])))))
--             ds
--   in runHF p4 $
--       foldr
--         (\e -> cons (\acc a b c d -> f a b c d e : acc))
--         (k (const (const (const (const [])))))
--         es
