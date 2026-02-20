{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}
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
    (partA @'[a])
    . flip
      (g
    . flip . flip id)
  where
  -- g :: PartATF '[a] (BaseFunTF '[b, a] (ProducerTF '[b, a] (c -> d))) (ProducerTF '[b, a] (c -> d))
  --     -- BaseFunTF '[a]
  --     --     ( BaseFunTF '[b, a] (ProducerTF '[b, a] (c -> d))
  --     --     -> ProducerTF '[b, a] (c -> d)
  --     --     )
  --     -- -> ProducerTF '[a] (b -> c -> d)
  --     -- -> BaseFunTF '[a]
  --     --     (ProducerTF '[a] (b -> c -> d))
  -- g = flip . (push .)
  -- g :: (b ->
  --         (a -> b -> ProducerTF [b, a] (c -> d))
  --         -> ProducerTF [b, a] (c -> d))
  --       -> b
  --       -> (a -> b -> ProducerTF [b, a] (c -> d))
  --       -> ProducerTF [b, a] (c -> d)
  g :: PartBTF '[] b (a -> b -> ProducerTF [b, a] (c -> d)) (ProducerTF [b, a] (c -> d))
  g = id

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
    (partA @[a,x])
    . flip
      (g
    . flip . flip id)
  where
   -- g :: --BaseFunTF [a,x] (ProducerTF [a,x] (b -> c -> d))
   --    BaseFunTF [a,x] (BaseFunTF [b,a,x] (ProducerTF '[b,a,x] (c -> d)) -> (ProducerTF '[b,a,x] (c -> d)))
   --    -> x -> ProducerTF '[a,x] (b -> c -> d)
   --    -> a -> ProducerTF '[a,x] (b -> c -> d)
   -- g = -- ((flip . (push .)) .)
   --     flip . ((flip . (push .)) .)
   g :: (a ->
          (x -> a -> b -> ProducerTF [b, a, x] (c -> d))
          -> b -> ProducerTF [b, a, x] (c -> d))
        -> b -> a
        -> (x -> a -> b -> ProducerTF [b, a, x] (c -> d))
        -> ProducerTF [b, a, x] (c -> d)
   g = flip . ((id . flip) .)

pushProducerFold'''
  :: forall a x b c d y.
    b -> Hyper
            (ProducerTF '[a,x,y] (b -> c -> d))
            (BaseFunTF '[x,y] (a -> ProducerTF '[a,x,y] (b -> c -> d)))
       -> Hyper
            (ProducerTF '[a,x,y] (b -> c -> d))
            (BaseFunTF '[x,y] (a -> ProducerTF '[a,x,y] (b -> c -> d)))
pushProducerFold''' =
  push . (partA @[a,x,y]) . flip (g . flip . flip id) --g
  where
   -- g :: PartATF '[a,x,y] a4 b1
   --      -- (y -> x -> a -> a4 -> b1)
   --      --               -> Hyper a4 b1 -> y -> x -> a -> Hyper a4 b1
   -- g = partA @[a,x,y] -- flip . (h .)
   --
   -- h :: PartATF '[a,x] a4 b1
   -- h = flip . (i .)
   --
   -- i :: PartATF '[a] a4 b1
   -- i = flip . (j .)
   --
   -- j :: PartATF '[] a4 b1
   -- j = push
   -- g :: ()
     --  b -> y -> x -> a -> (y -> x -> a -> b -> ProducerTF [b,a,x,y] (c -> d))
     -- -> ProducerTF [b,a,x,y] (c -> d)
   -- g :: (x ->
   --        (y -> x -> a -> b -> ProducerTF [b,a,x,y] (c -> d))
   --      -> a
   --      -> b
   --      -> ProducerTF [b,a,x,y] (c -> d)
   --      )
   --    -> b -> x -> a ->
   --      (y -> x -> a -> b -> ProducerTF [b,a,x,y] (c -> d))
   --      -> ProducerTF [b,a,x,y] (c -> d)
   g :: PartBTF
          [b, a] x
          (y -> x -> a -> b -> ProducerTF [b,a,x,y] (c -> d))
          (ProducerTF [b,a,x,y] (c -> d))
   g = flip . ((gg . flip) .)

   gg :: PartBTF '[b] a
           (y -> x -> a -> b -> ProducerTF [b,a,x,y] (c -> d))
           (ProducerTF [b,a,x,y] (c -> d))
        -- (a -> (y -> x -> a -> b -> ProducerTF [b, a, x, y] ( c -> d))
        --    -> b
        --    -> ProducerTF [b, a, x, y] (c -> d))
        --   -> b
        --   -> a
        --   -> (y -> x -> a -> b -> ProducerTF [b, a, x, y] (c -> d))
        --   -> ProducerTF [b, a, x, y] (c -> d)
   gg = flip . (flip .)

   -- ggg = flip . ((id . flip) .)
   -- g b y x a f = f y x a b -- flip . ((flip . (flip .) . flip) .)

type family PartATF args h1 h2 where
  PartATF args h1 h2 =
    BaseFunTF args
         ( h1 -> h2)
    -> Hyper h1 h2
    -> BaseFunTF args (Hyper h1 h2)

-- t1 is penultimate, t2 is ultimate arg
type family PartBTF args t1 h1 h2 where
  PartBTF args t1 h1 h2 =
    ( t1
      -> h1
      -> BaseFunTF args h2)
    -> BaseFunTF (Take1TF args)
        ( t1 -> BaseFunTF (Drop1TF args) (h1 -> h2))

type family Take1TF args where
  Take1TF (a ': args) = '[a]
  Take1TF '[] = '[]

type family Drop1TF args where
  Drop1TF (a ': args) = args
  Drop1TF '[] = '[]

class FoldComponents args h1 h2 where
  partA :: PartATF args h1 h2

instance FoldComponents '[] h1 h2 where
  partA = push

instance
    ( '(argsInit, a) ~ UnsnocTF (x ': args)
    , FoldComponents argsInit h1 h2
    , BaseFunTF (x ': args) (h1 -> h2) ~ (a -> BaseFunTF argsInit (h1 -> h2))
    , BaseFunTF (x ': args) (Hyper h1 h2) ~ (a -> BaseFunTF argsInit (Hyper h1 h2))
    )
  => FoldComponents (x ': args) h1 h2 where
  partA f h (a :: a) = (partA @argsInit @h1 @h2) (f a) h

class FoldComponentB args t1 h1 h2 where
  partB :: PartBTF args t1 h1 h2

instance FoldComponentB '[] x h1 h2 where
  partB = id

instance
  ( '(argsInit, a) ~ UnsnocTF (x ': args)
  , FoldComponentB argsInit a h1 h2
  , BaseFunTF (Take1TF argsInit) (a -> BaseFunTF (Drop1TF argsInit) (h1 -> h2))
      ~ (x -> BaseFunTF args (h1 -> h2))
  , BaseFunTF args (x -> h2)
      ~ (a -> BaseFunTF argsInit h2)
  )
  => FoldComponentB (x ': args) y h1 h2 where
  partB = flip . ((partB @argsInit @a @h1 @h2 . flip) .)

type UnsnocTF :: [Type] -> ([Type], Type)
type family UnsnocTF xs where
  UnsnocTF '[x] = '( '[], x)
  UnsnocTF (x ': xs) = ConsFstTF x (UnsnocTF xs)

type ConsFstTF :: Type -> ([Type], Type) -> ([Type], Type)
type family ConsFstTF x t = res | res -> x t where
  ConsFstTF x '(acc, r) = '(x ': acc, r)

-- instance FoldComponents args h1 h2 => FoldComponents (x ': args) h1 h2 where
--   partA =  flip . ((partA @args @h1 @h2) .)

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
