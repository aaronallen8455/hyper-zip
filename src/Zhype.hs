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
  ProducerTF args (y -> ResultTy res) = [res]
  ProducerTF args (x -> fun) =
    Hyper
      (BaseFunTF (x ': args) (ProducerTF (x ': args) fun))
      (ProducerTF (x ': args) fun)
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

zipWith2 :: forall a b c. (a -> b -> c) -> [a] -> [b] -> [c]
zipWith2 f as bs =
  let p1 = --initProducer @(a -> b -> c -> ResultTy d)
        foldr
          (\x -> push ($ x))
          (constProducer @'[] @(a -> b -> ResultTy c))
          as
      pa :: (a -> c) -> a -> [c] -> [c]
      pa = ((:) .)
      pb :: (b -> c) -> b -> c
      pb = id
  in invoke p1
       (foldr
          -- (\b -> push (\r a -> f a b : r))
          (push . flip .
              pa
              . flip (pb . f))
          (k (const []))
          bs)

-- push . flip .
-- ((:) .)
-- . flip f

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
      paa :: (b -> d) -> b -> [d] -> [d]
      paa = ((:) .)
      pa :: (a -> b -> d) -> a -> [d] -> b -> [d]
      pa = ((flip . paa) .)
      pbb :: (c -> d) -> c -> d
      pbb = id
      pb :: (b -> c -> d) -> c -> b -> d
      pb = (flip . (pbb .))
  in invoke p2
       (foldr
          (push . flip .
              pa
              . flip (pb . f))
          (k (const $ const []))
          cs
        )

-- push . flip .
-- ((flip . ((:) .)) .)
-- . flip (flip . f)

class HyperZip fun where
  hyperZip :: fun -> ListArgsTF fun

type family ListArgsTF fun where
  ListArgsTF (a -> b) = [a] -> ListArgsTF b
  ListArgsTF a = [a]

-- [x] ->
-- ProducerTF args (x -> y -> fun)
-- ->
-- ProducerTF (x : args) (y -> fun)

-- produce
--   :: forall args x fun.
--   ProducerTF args (x -> fun)
--   -> [x]
--   -> ProducerTF (x ': args) fun
-- produce p xs =
--   invoke p $
--     foldr
--       (push .
--         (partA @args)
--         . flip
--           ( partB @(DropLast2TF (x ': args))
--             . flip . flip id)
--         )
--       (k $ constArgHyp @args @args @fun)
--       xs

class Produce args x y fun where
  produce
    :: ProducerTF args (x -> y -> fun)
    -> [y]
    -> ProducerTF (x ': args) (y -> fun)

instance
  ( '(initArgs, x) ~ UnsnocTF (a ': args)
  , BaseFunTF (Take1TF (DropLast2TF (b : a : args))) (a -> BaseFunTF (Drop1TF (DropLast2TF (b : a : args))) ((x -> a -> BaseFunTF (DropLast2TF (b : a : args)) [d]) -> [d]))
      ~ (b -> BaseFunTF initArgs (BaseFunTF args (a -> b -> [d]) -> [d]))
  , BaseFunTF args (a -> BaseFunTF args (a -> b -> [d]) -> [d])
      ~ (x -> BaseFunTF initArgs (BaseFunTF args (a -> b -> [d]) -> [d]))
  , BaseFunTF args (a -> Hyper (BaseFunTF args (a -> b -> [d])) [d])
      ~ (x -> BaseFunTF initArgs (Hyper (BaseFunTF args (a -> b -> [d])) [d]))
  , ConstBaseFunc initArgs (a : args) (b -> c -> ResultTy d)
  , FoldComponentB
      (DropLast2TF (b : a : args))
      a
      (x -> a -> BaseFunTF (DropLast2TF (b : a : args)) [d])
      [d]
  , FoldComponents initArgs (BaseFunTF args (a -> b -> [d])) [d]
  )
  => Produce args a b (c -> ResultTy d) where
  produce p bs = invoke p $
    foldr
      (push .
        (partA @(a ': args) @(BaseFunTF args (a -> b -> [d])) @[d])
        . flip
          ( (partB @(DropLast2TF (b ': a ': args)) @a @_ @(ProducerTF (b ': a ': args) (c -> ResultTy d)))
            . flip . flip id)
        )
      (k (constArgHyp @(a ': args) @(a ': args) @(b -> c -> ResultTy d)))
      bs

produce'
  :: forall args x y fun initArgs l.
    ( '(initArgs, l) ~ UnsnocTF (x ': args)
    , BaseFunTF args (x -> ProducerTF (x : args) (y -> fun))
        ~ (l -> BaseFunTF initArgs (ProducerTF (x : args) (y -> fun)))
    , ConstBaseFunc initArgs (x : args) (y -> fun)
    , BaseFunTF args
        (x -> BaseFunTF args
                (x -> y -> ProducerTF (y : x : args) fun)
                -> ProducerTF (y : x : args) fun
        ) ~ (l -> BaseFunTF initArgs
                    (BaseFunTF args (x -> y -> ProducerTF (y : x : args) fun)
                    -> ProducerTF (y : x : args) fun))
    , BaseFunTF args
        (x -> Hyper (BaseFunTF args (x -> y -> ProducerTF (y : x : args) fun))
                    (ProducerTF (y : x : args) fun)
        ) ~ (l -> BaseFunTF initArgs
                    (Hyper (BaseFunTF args (x -> y -> ProducerTF (y : x : args) fun))
                           (ProducerTF (y : x : args) fun)
                    )
            )
      -- Precludes the case where ProducerTF gives the result list
    , ProducerTF (x : args) (y -> fun)
        ~ Hyper (BaseFunTF args (x -> y -> ProducerTF (y : x : args) fun))
                (ProducerTF (y : x : args) fun)
    , FoldComponents
        initArgs
        (BaseFunTF args (x -> y -> ProducerTF (y : x : args) fun))
        (ProducerTF (y : x : args) fun)
    , BaseFunTF (Take1TF (DropLast2TF (y : x : args)))
        (x -> BaseFunTF (Drop1TF (DropLast2TF (y : x : args)))
                ((l -> x -> BaseFunTF (DropLast2TF (y : x : args))
                              (ProducerTF (y : x : args) fun)
                 ) -> ProducerTF (y : x : args) fun
                )
        ) ~ (y -> BaseFunTF initArgs
                    (BaseFunTF args (x -> y -> ProducerTF (y : x : args) fun)
                      -> ProducerTF (y : x : args) fun
                    )
            )
    , FoldComponentB
        (DropLast2TF (y : x : args))
        x
        (l -> x -> BaseFunTF (DropLast2TF (y : x : args)) (ProducerTF (y : x : args) fun))
        (ProducerTF (y : x : args) fun)
    )
  => ProducerTF args (x -> y -> fun)
  -> [y]
  -> ProducerTF (x ': args) (y -> fun)
produce' p ys = invoke p $
  foldr
    (push .
      (partA @(x ': args) @_ @(ProducerTF (y ': x ': args) fun))
      . (\e a -> partB @(DropLast2TF (y ': x ': args)) @x @_ @(ProducerTF (y ': x ': args) fun)
          (\b f -> f a b) e
        )
    )
    (k (constArgHyp @(x ': args) @(x ': args) @(y -> fun)))
    ys

type family DropLast2TF args where
  DropLast2TF '[a, b] = '[]
  DropLast2TF (x ': xs) = x ': DropLast2TF xs

-- Might need to collect the arguments with class before building hyper functions
-- - or - take the previous hyper function as the first argument and the list
-- as the second, the process in order.

zipWith4 :: forall a b c d e. (a -> b -> c -> d -> e) -> [a] -> [b] -> [c] -> [d] -> [e]
zipWith4 f as bs cs ds =
  let p1 =
        foldr
          (\x -> push ($ x))
          (constProducer @'[] @(a -> b -> c -> d -> ResultTy e))
          as
      p2 :: ProducerTF '[a] (b -> c -> d -> ResultTy e)
      p2 = invoke p1 $
            foldr
              (push .
                (partA @'[a])
                . flip
                  ( partB @'[] @b @_ @(Hyper (a -> b -> c -> [e]) [e])
                    . flip . flip id)
                )
              (k $ constArgHyp @'[a] @'[a] @(b -> c -> d -> ResultTy e))
              bs
      p3 :: ProducerTF '[b,a] (c -> d -> ResultTy e)
      p3 = produce @'[a] @b @c @(d -> ResultTy e) p2 cs
            -- foldr
            --   (push .
            --     (partA @'[b, a] @(a -> b -> c -> [e]) @[e])
            --     . flip
            --       ( partB @'[c] @b @(a -> b -> c -> [e]) @[e]
            --         . flip . flip id)
            --     )
            --   (k $ constArgHyp @'[b,a] @'[b,a] @(c -> d -> ResultTy e))
            --   cs
  in invoke p3
       (foldr
          (push .
              (resultPartA @[e,d,c,b,a])
              . flip ((resultPartB @[e,d,c,b]) . f))
          (k mempty)
          ds
        )

-- args in reverse order, e.g. [e,d,c,b,a]
type family ResultPartATF args where
  ResultPartATF (resTy ': _ ': args) =
    BaseFunTF args resTy -> [resTy] -> BaseFunTF args [resTy]

-- args should be the init of those passed to part A
type family ResultPartBTF args where
  ResultPartBTF (resTy ': pen ': args) =
    BaseFunTF (pen ': args) resTy -> pen -> BaseFunTF args resTy

class ResultPartA args where
  resultPartA :: ResultPartATF args

instance ResultPartA '[a, b, c] where
  resultPartA f xs c = f c : xs

instance
  ( '(restInit, x) ~ UnsnocTF (d ': rest)
  , BaseFunTF rest (d -> c -> a)
    ~ (x -> BaseFunTF restInit (c -> a))
  , BaseFunTF rest (d -> c -> [a])
    ~ (x -> BaseFunTF restInit (c -> [a]))
  , ResultPartA (a ': b ': c ': restInit)
  ) => ResultPartA (a ': b ': c ': d ': rest) where
  resultPartA = flip . (resultPartA @(a ': b ': c ': restInit) .)

class ResultPartB args where
  resultPartB :: ResultPartBTF args

instance ResultPartB '[a, b] where
  resultPartB = id

instance
  ( '(restInit, x) ~ UnsnocTF (c ': rest)
  , BaseFunTF rest (c -> a)
    ~ (x -> BaseFunTF restInit a)
  , BaseFunTF rest (c -> b -> a)
    ~ (x -> BaseFunTF restInit (b -> a))
  , ResultPartB (a ': b ': restInit)
  ) => ResultPartB (a ': b ': c ': rest) where
  resultPartB = flip . (resultPartB @(a ': b ': restInit) .)

-- push . flip .
-- ((flip . ((flip . ((:) .)) .)) .)
-- . flip (flip . (flip .) . f)

zipWith5 :: forall a b c d e f. (a -> b -> c -> d -> e -> f) -> [a] -> [b] -> [c] -> [d] -> [e] -> [f]
zipWith5 f as bs cs ds es =
  let p1 =
        foldr
          (\x -> push ($ x))
          (constProducer @'[] @(a -> b -> c -> d -> e -> ResultTy f))
          as
      p2 = invoke p1 $
            foldr
              (push .
                (partA @'[a])
                . flip
                  ( partB @'[]
                    . flip . flip id)
                )
              (k $ constArgHyp @'[a] @'[a] @(b -> c -> d -> e -> ResultTy f))
              bs
      p3 = invoke p2 $
            foldr
              (push .
                (partA @'[b, a])
                . flip
                  ( partB @'[c] @b
                    . flip . flip id)
                )
              (k $ constArgHyp @'[b,a] @'[b,a] @(c -> d -> e -> ResultTy f))
              cs
      p4 = invoke p3 $
            foldr
              (push .
                (partA @'[c,b,a])
                . flip
                  ( partB @'[d,c] @b
                    . flip . flip id)
                )
              (k $ constArgHyp @'[c,b,a] @'[c,b,a] @(d -> e -> ResultTy f))
              ds
  in invoke p4
       (foldr (\e -> push (\r a b c d -> f a b c d e : r)) (k (const $ const $ const $ const [])) es)

-- push . flip .
-- ((flip . ((flip . ((flip . ((:) .)) .)) .)) .)
-- . flip (flip . ((flip . (flip .)) .) . f)

zipWith6 :: forall a b c d e f g. (a -> b -> c -> d -> e -> f -> g) -> [a] -> [b] -> [c] -> [d] -> [e] -> [f] -> [g]
zipWith6 f as bs cs ds es fs =
  let p1 =
        foldr
          (\x -> push ($ x))
          (constProducer @'[] @(a -> b -> c -> d -> e -> f -> ResultTy g))
          as
      p2 = invoke p1 $
            foldr
              (push .
                (partA @'[a])
                . flip
                  ( partB @'[] @b @(a -> b -> ProducerTF [b,a] (c -> d -> e -> f -> ResultTy g)) @(ProducerTF [b,a] (c -> d -> e -> f -> ResultTy g))
                    . flip . flip id)
                )
              (k $ constArgHyp @'[a] @'[a] @(b -> c -> d -> e -> f -> ResultTy g))
              bs
      p3 = invoke p2 $
            foldr
              (push .
                (partA @'[b, a])
                . flip
                  ( partB @'[c] @b @(a -> b -> c -> ProducerTF [c,b,a] (d -> e -> f -> ResultTy g)) @(ProducerTF [c,b,a] (d -> e -> f -> ResultTy g))
                    . flip . flip id)
                )
              (k $ constArgHyp @'[b,a] @'[b,a] @(c -> d -> e -> f -> ResultTy g))
              cs
      p4 = invoke p3 $
            foldr
              (push .
                (partA @'[c,b,a])
                . (\d a -> partB @'[d,c] @b (\b f -> f a b) d)
                )
              (k $ constArgHyp @'[c,b,a] @'[c,b,a] @(d -> e -> f -> ResultTy g))
              ds
      b5 :: (b -> (a -> b -> c -> d -> e -> [g]) -> c -> d -> e -> [g])
              -> e -> b -> c -> d -> (a -> b -> c -> d -> e -> [g]) -> [g]
      b5 = partB @'[e,d,c] @b
      p5 = invoke p4 $
            foldr
              (push .
                (partA @'[d,c,b,a])
                . (\e a -> b5 (\b f -> f a b) e)
                  -- (\x y -> b5
                  --   $ (\b a f -> f b a) x y)
                )
              (k $ constArgHyp @'[d,c,b,a] @'[d,c,b,a] @(e -> f -> ResultTy g))
              es
  in invoke p5
       (foldr (\ff -> push (\r a b c d e -> f a b c d e ff : r)) (k (const $ const $ const $ const $ const [])) fs)

-- push . flip .
-- ((flip . ((flip . ((flip . ((flip . ((:) .)) .)) .)) .)) .)
-- . flip (flip . ((flip . ((flip . (flip .)) .)) .) . f)

-- push .
-- {partA}
-- . flip ({partB} . f)
--
-- base partA = ((:) .)
-- (flip . ({partA} .))
--
-- base partB = id
-- (flip . ({partB} .))

type family PartATF args h1 h2 where
  PartATF args h1 h2 =
    BaseFunTF args
         ( h1 -> h2)
    -> Hyper h1 h2
    -> BaseFunTF args (Hyper h1 h2)

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
  partB f x y = partB @argsInit @a @h1 @h2 (flip $ f y) x

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
