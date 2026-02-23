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
  ProducerTF args (x -> y -> ResultTy res) = Hyper (BaseFunTF (x ': args) [res]) [res]
  ProducerTF args (x -> y -> fun) =
    Hyper
      (BaseFunTF (x ': args) (ProducerTF (x ': args) (y -> fun)))
      (ProducerTF (x ': args) (y -> fun))
  -- ProducerTF args (v -> ResultTy res) = Hyper (BaseFunTF args [res]) [res]
  -- TODO: error case

type BaseFunTF :: [Type] -> Type -> Type
type family BaseFunTF args rest where
  BaseFunTF (x ': args) rest = BaseFunTF args (x -> rest)
  BaseFunTF '[] done = done

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
  ConstProducer args (a -> b -> ResultTy res) where
  constProducer = k []

instance
  ConstProducer (a ': args) (b -> c -> d)
  => ConstProducer args (a -> b -> c -> d) where
  constProducer = k (constProducer @(a ': args) @(b -> c -> d))

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

class ConstBaseFunc baseFunArgs args fun where
  constArgHyp :: BaseFunTF baseFunArgs (ProducerTF args fun)

instance ConstProducer args fun => ConstBaseFunc '[] args fun where
  constArgHyp = constProducer @args @fun

instance
  ( ConstBaseFunc initFunArgs args fun
  , '(initFunArgs, b) ~ UnsnocTF (a ': baseFunArgs)
  , BaseFunTF (a ': baseFunArgs) (ProducerTF args fun)
      ~ (b -> BaseFunTF initFunArgs (ProducerTF args fun))
  )
  => ConstBaseFunc (a ': baseFunArgs) args fun where
  constArgHyp = const (constArgHyp @initFunArgs @args @fun)

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
            (ProducerTF '[a] (b -> c -> ResultTy d))
            (BaseFunTF '[] (a -> ProducerTF '[a] (b -> c -> ResultTy d)))
       -> Hyper
            (ProducerTF '[a] (b -> c -> ResultTy d))
            (BaseFunTF '[] (a -> ProducerTF '[a] (b -> c -> ResultTy d)))
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
  -- g :: PartBTF '[] b (a -> b -> ProducerTF [b, a] (c -> d)) (ProducerTF [b, a] (c -> d))
  g = id

pushProducerFold''
  :: forall a x b c d.
    b -> Hyper
            (ProducerTF '[a,x] (b -> c -> ResultTy d))
            (BaseFunTF '[x] (a -> ProducerTF '[a,x] (b -> c -> ResultTy d)))
       -> Hyper
            (ProducerTF '[a,x] (b -> c -> ResultTy d))
            (BaseFunTF '[x] (a -> ProducerTF '[a,x] (b -> c -> ResultTy d)))
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

   -- g :: (a ->
   --        (x -> a -> b -> ProducerTF [b, a, x] (c -> ResultTy d))
   --        -> b -> ProducerTF [b, a, x] (c -> ResultTy d))
   --      -> b -> a
   --      -> (x -> a -> b -> ProducerTF [b, a, x] (c -> ResultTy d))
   --      -> ProducerTF [b, a, x] (c -> ResultTy d)
   g = flip . ((id . flip) .)

pushProducerFold'''
  :: forall a x b c d y.
    b -> Hyper
            (ProducerTF '[a,x,y] (b -> c -> ResultTy d))
            (BaseFunTF '[x,y] (a -> ProducerTF '[a,x,y] (b -> c -> ResultTy d)))
       -> Hyper
            (ProducerTF '[a,x,y] (b -> c -> ResultTy d))
            (BaseFunTF '[x,y] (a -> ProducerTF '[a,x,y] (b -> c -> ResultTy d)))
pushProducerFold''' =
  push . (partA @[a,x,y])
       . flip (partB @[b, a] @x . flip . flip id)

-- Hyper
--     (a
--      -> Hyper
--           (a -> b -> Hyper (a -> b -> [d]) [d]) (Hyper (a -> b -> [d]) [d]))
--     (Hyper
--        (a -> b -> Hyper (a -> b -> [d]) [d]) (Hyper (a -> b -> [d]) [d]))
--
-- Hyper
--     (a
--      -> Hyper
--           (a -> b -> Hyper (a -> b -> [d]) [d]) (Hyper (a -> b -> [d]) [d]))
--     (Hyper (a -> b -> [d]) [d])

zipWith3 :: forall a b c d. (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
zipWith3 f as bs cs =
  let p1 -- :: ProducerTF '[] (a -> b -> c -> ResultTy d) -- Hyper (a -> Hyper (a -> b -> [d]) [d]) (Hyper (a -> b -> [d]) [d])
          :: Hyper (a -> Hyper (a -> b -> [d]) [d]) (Hyper (a -> b -> [d]) [d])
      p1 = --initProducer @(a -> b -> c -> ResultTy d)
        foldr
          (\x -> push ($ x))
          (constProducer @'[] @(a -> b -> c -> ResultTy d))
          as
      p2 :: Hyper (a -> b -> [d]) [d]
      p2 = invoke p1 $
            foldr
              (push .
                (partA @'[a]) --(\f h a -> push (f a) h)
                . flip
                  ( partB @'[]
                    . flip . flip id)
                )
              (k $ constArgHyp @'[a] @'[a] @(b -> c -> ResultTy d))
              bs
  in invoke p2
       (foldr (\c -> push (\r a b -> f a b c : r)) (k (const $ const [])) cs)

zipWith4 :: forall a b c d e. (a -> b -> c -> d -> e) -> [a] -> [b] -> [c] -> [d] -> [e]
zipWith4 f as bs cs ds =
  let p1 =
        foldr
          (\x -> push ($ x))
          (constProducer @'[] @(a -> b -> c -> d -> ResultTy e))
          as
      p2 = invoke p1 $
            foldr
              (push .
                (partA @'[a])
                . flip
                  ( partB @'[]
                    . flip . flip id)
                )
              (k $ constArgHyp @'[a] @'[a] @(b -> c -> d -> ResultTy e))
              bs
      p3 = invoke p2 $
            foldr
              (push .
                (partA @'[b, a])
                . flip
                  ( partB @'[c]
                    . flip . flip id)
                )
              (k $ constArgHyp @'[b,a] @'[b,a] @(c -> d -> ResultTy e))
              cs
  in invoke p3
       (foldr (\d -> push (\r a b c -> f a b c d : r)) (k (const $ const $ const [])) ds)

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
