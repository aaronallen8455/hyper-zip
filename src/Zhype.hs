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
  ProducerTF args (v -> res) = Hyper (BaseFunTF args [res]) [res]
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

instance {-# OVERLAPPABLE #-}
  ProducerTF args (a -> res) ~ Hyper (BaseFunTF args [res]) [res]
  => ConstProducer args (a -> res) where
  constProducer = k []

instance {-# OVERLAPPING #-}
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

class AppendProducer a args funTy where
  appendProducer :: [a] -> ProducerTF args (a -> funTy) -> ProducerTF (a ': args) funTy

-- type family ZipWithHypTyTF args res where
--   ZipWithHypTyTF '[] res = [res]
--   ZipWithHypTyTF (x ': xs) res = x -> ZipWithHypTyTF xs res

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
