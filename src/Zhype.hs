{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Zhype
  ( zipWithN
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

initProducer
  :: forall funTy firstArg funRest.
  ( ConstProducer '[] funTy
  , (firstArg -> funRest) ~ funTy
  , ProducerTF '[] funTy ~
      Hyper
        (BaseFunTF '[firstArg] (ProducerTF '[firstArg] funRest))
        (ProducerTF '[firstArg] funRest)
  )
  => [firstArg] -> ProducerTF '[] funTy
initProducer =
  foldr
    (\x -> push ($ x))
    (constProducer @'[] @funTy)

consumer
  :: forall args x y r fun initArgs l
   . ( '(initArgs, l) ~ UnsnocTF (x ': args)
     , fun ~ (l -> BaseFunTF initArgs (y -> r))
     , BaseFunTF args (x -> r) ~ (l -> BaseFunTF initArgs r)
     , Monoid (BaseFunTF args (x -> [r]))
     , ResultPartB (r : y : initArgs)
     , ResultPartA (r : y : x : args)
     )
  => fun -> ProducerTF args (x -> y -> ResultTy r) -> [y] -> [r]
consumer f p ys = invoke p $
  foldr
    (push .
        (resultPartA @(r ': y ': x ': args))
        . (\y (l :: l) -> (resultPartB @(r ': y ': initArgs)) (f l) y)
        )
    (k mempty)
    ys

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

produceFinish
  :: forall args (xx :: *) a b c d initArgs x.
    ( '(initArgs, x) ~ UnsnocTF (a ': args)
    , BaseFunTF (Take1TF (DropLast2TF (b : a : args)))
        (xx
         -> BaseFunTF
              (Drop1TF (DropLast2TF (b : a : args)))
              ((x -> xx -> BaseFunTF (DropLast2TF (b : a : args)) [d]) -> [d]))
      ~ (b -> BaseFunTF initArgs (BaseFunTF args (a -> b -> [d]) -> [d]))
    , BaseFunTF args (a -> BaseFunTF args (a -> b -> [d]) -> [d])
      ~ (x -> BaseFunTF initArgs (BaseFunTF args (a -> b -> [d]) -> [d]))
    , BaseFunTF args (a -> Hyper (BaseFunTF args (a -> b -> [d])) [d])
      ~ (x -> BaseFunTF initArgs (Hyper (BaseFunTF args (a -> b -> [d])) [d]))
    , ConstBaseFunc initArgs (a : args) (b -> c -> ResultTy d)
    , FoldComponentB (DropLast2TF (b : a : args)) xx
        (x -> xx -> BaseFunTF (DropLast2TF (b : a : args)) [d])
        [d]
    , FoldComponents initArgs (BaseFunTF args (a -> b -> [d])) [d]
    )
  => ProducerTF args (a -> b -> c -> ResultTy d)
  -> [b]
  -> ProducerTF (a ': args) (b -> c -> ResultTy d)
produceFinish p bs = invoke p $
    foldr
      (push .
        (partA @(a ': args) @(BaseFunTF args (a -> b -> [d])) @[d])
        . flip
          ( (partB @(DropLast2TF (b ': a ': args)) @xx @_ @(ProducerTF (b ': a ': args) (c -> ResultTy d)))
            . flip . flip id)
        )
      (k (constArgHyp @(a ': args) @(a ': args) @(b -> c -> ResultTy d)))
      bs

produceInter
  :: forall args xx x y fun initArgs l.
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
        (xx
         -> BaseFunTF
              (Drop1TF (DropLast2TF (y : x : args)))
              ((l
                -> xx
                -> BaseFunTF
                     (DropLast2TF (y : x : args)) (ProducerTF (y : x : args) fun))
               -> ProducerTF (y : x : args) fun))
      ~ (y
         -> BaseFunTF
              initArgs
              (BaseFunTF args (x -> y -> ProducerTF (y : x : args) fun)
               -> ProducerTF (y : x : args) fun))
    , FoldComponentB
        (DropLast2TF (y : x : args))
        xx
        (l -> xx -> BaseFunTF (DropLast2TF (y : x : args)) (ProducerTF (y : x : args) fun))
        (ProducerTF (y : x : args) fun)
    )
  => ProducerTF args (x -> y -> fun)
  -> [y]
  -> ProducerTF (x ': args) (y -> fun)
produceInter p ys = invoke p $
  foldr
    (push .
      (partA @(x ': args) @_ @(ProducerTF (y ': x ': args) fun))
      . (\e a -> partB @(DropLast2TF (y ': x ': args)) @xx @_ @(ProducerTF (y ': x ': args) fun)
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

-- BaseFunTF (Take1TF (DropLast2TF (b : a : '[]))) (a -> BaseFunTF (Drop1TF (DropLast2TF (b : a : '[]))) ((a -> a -> BaseFunTF (DropLast2TF (b : a : '[])) (ProducerTF (b : a : '[]) (c -> d -> ResultTy e))) -> ProducerTF (b : a : '[]) (c -> d -> ResultTy e)))
-- = a
--   -> (a -> a -> Hyper (a -> b -> c -> [e]) [e])
--   -> Hyper (a -> b -> c -> [e]) [e]
--
-- ~ (y -> BaseFunTF initArgs
--                     (BaseFunTF args (x -> y -> ProducerTF (y : x : args) fun)
--                       -> ProducerTF (y : x : args) fun
--                     )
--             )

zipWith4 :: forall a b c d e. (a -> b -> c -> d -> e) -> [a] -> [b] -> [c] -> [d] -> [e]
zipWith4 f as bs cs ds =
  let p1 :: ProducerTF '[] (a -> b -> c -> d -> ResultTy e)
      p1 =
        foldr
          (\x -> push ($ x))
          (constProducer @'[] @(a -> b -> c -> d -> ResultTy e))
          as
      p2 :: ProducerTF '[a] (b -> c -> d -> ResultTy e)
      p2 = --produceInter @'[] @a @b @(c -> d -> ResultTy e) p1 bs
            invoke p1 $
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
      p3 = produceFinish @'[a] p2 cs
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
              . (\d a -> (resultPartB @[e,d,c,b]) (f a) d)
              )
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
  let p1 = initProducer @(a -> b -> c -> d -> e -> f -> ResultTy g) as
        -- foldr
        --   (\x -> push ($ x))
        --   (constProducer @'[] @(a -> b -> c -> d -> e -> f -> ResultTy g))
        --   as
      p2 = produceInter @'[] @b @a @b @(c -> d -> e -> f -> ResultTy g) p1 bs
           -- invoke p1 $
           --  foldr
           --    (push .
           --      (partA @'[a])
           --      . flip
           --        ( partB @'[] @b @(a -> b -> ProducerTF [b,a] (c -> d -> e -> f -> ResultTy g)) @(ProducerTF [b,a] (c -> d -> e -> f -> ResultTy g))
           --          . flip . flip id)
           --      )
           --    (k $ constArgHyp @'[a] @'[a] @(b -> c -> d -> e -> f -> ResultTy g))
           --    bs
    -- , BaseFunTF (Take1TF (DropLast2TF (c : b : '[a]))) (b -> BaseFunTF (Drop1TF (DropLast2TF (c : b : '[a]))) ((a -> b -> BaseFunTF (DropLast2TF (c : b : '[a])) (ProducerTF (c : b : '[a]) (d -> e -> f -> ResultTy g))) -> ProducerTF (c : b : '[a]) (d -> e -> f -> ResultTy g)))
      p3 = produceInter @'[a] @b @b @c @(d -> e -> f -> ResultTy g) p2 cs
           -- invoke p2 $
           --  foldr
           --    (push .
           --      (partA @'[b, a])
           --      . flip
           --        ( partB @'[c] @b @(a -> b -> c -> ProducerTF [c,b,a] (d -> e -> f -> ResultTy g)) @(ProducerTF [c,b,a] (d -> e -> f -> ResultTy g))
           --          . flip . flip id)
           --      )
           --    (k $ constArgHyp @'[b,a] @'[b,a] @(c -> d -> e -> f -> ResultTy g))
           --    cs
           --
    -- , BaseFunTF (Take1TF (DropLast2TF (d : c : [b,a]))) (c -> BaseFunTF (Drop1TF (DropLast2TF (d : c : [b,a]))) ((a -> c -> BaseFunTF (DropLast2TF (d : c : [b,a])) (ProducerTF (d : c : [b,a]) (e -> f -> ResultTy g))) -> ProducerTF (d : c : [b,a]) (e -> f -> ResultTy g)))
    -- ~ (d -> BaseFunTF initArgs
    --                 (BaseFunTF [b,a] (c -> d -> ProducerTF (d : c : [b,a]) (d -> e -> f -> ResultTy g))
    --                   -> ProducerTF (d : c : [b,a]) (d -> e -> f -> ResultTy g)
    --                 )
    --         )
      p4 :: ProducerTF '[c, b, a] (d -> e -> f -> ResultTy g)
      p4 = produceInter @'[b, a] @b @c @d @(e -> f -> ResultTy g) p3 ds
           -- invoke p3 $
           --  foldr
           --    (push .
           --      (partA @'[c,b,a])
           --      . (\d a -> partB @'[d,c] @b (\b f -> f a b) d)
           --      )
           --    (k $ constArgHyp @'[c,b,a] @'[c,b,a] @(d -> e -> f -> ResultTy g))
           --    ds
      p5 :: ProducerTF '[d, c, b, a] (e -> f -> ResultTy g)
      p5 = produceFinish @'[c, b, a] p4 es
           -- invoke p4 $
           --  foldr
           --    (push .
           --      (partA @'[d,c,b,a])
           --      . (\e a -> partB @'[e,d,c] @b (\b f -> f a b) e)
           --      )
           --    (k $ constArgHyp @'[d,c,b,a] @'[d,c,b,a] @(e -> f -> ResultTy g))
           --    es
  in consumer @'[d,c,b,a] f p5 fs
     -- invoke p5
     --   (foldr (\ff -> push (\r a b c d e -> f a b c d e ff : r)) (k (const $ const $ const $ const $ const [])) fs)

class Produce fullFun args xx x y funTy where
  produce
    :: fullFun
    -> ProducerTF args (x -> y -> funTy)
    -> [y]
    -> ResultFunTF funTy

type family ResultFunTF funTy where
  ResultFunTF (a -> b) = [a] -> ResultFunTF b
  ResultFunTF (ResultTy a) = [a]

instance
  ( '(initArgs, l) ~ UnsnocTF (a ': args)
  , fullFun ~ (l -> BaseFunTF initArgs (b -> c))
  , BaseFunTF args (a -> c) ~ (l -> BaseFunTF initArgs c)
  , Monoid (BaseFunTF args (a -> [c]))
  , ResultPartB (c : b : initArgs)
  , ResultPartA (c : b : a : args)
  )
  => Produce fullFun args xx a b (ResultTy c) where
  produce = consumer @args @a @b @c @fullFun @initArgs @l

instance
  ( '(initArgs, l) ~ UnsnocTF (a ': args)
  , BaseFunTF args (a -> Hyper (BaseFunTF args (a -> b -> [d])) [d])
      ~ (l -> BaseFunTF initArgs (Hyper (BaseFunTF args (a -> b -> [d])) [d]))
  , Produce fullFun (a ': args) xx b c (ResultTy d)
  , BaseFunTF args (a -> BaseFunTF args (a -> b -> [d]) -> [d])
      ~ (l -> BaseFunTF initArgs (BaseFunTF args (a -> b -> [d]) -> [d]))
  , BaseFunTF (Take1TF (DropLast2TF (b : a : args)))
      (xx -> BaseFunTF (Drop1TF (DropLast2TF (b : a : args)))
               ((l -> xx -> BaseFunTF (DropLast2TF (b : a : args)) [d]) -> [d]))
      ~ (b -> BaseFunTF initArgs (BaseFunTF args (a -> b -> [d]) -> [d]))
  , ConstBaseFunc initArgs (a : args) (b -> c -> ResultTy d)
  , FoldComponentB
      (DropLast2TF (b : a : args))
      xx
      (l -> xx -> BaseFunTF (DropLast2TF (b : a : args)) [d])
      [d]
  , FoldComponents initArgs (BaseFunTF args (a -> b -> [d])) [d]
  )
  => Produce fullFun args xx a b (c -> ResultTy d) where
  produce f p
    = produce @fullFun @(a ': args) @xx @b @c @(ResultTy d) f
    . produceFinish @args @xx @a @b @c @d @initArgs @l p

instance
  ( '(initArgs, l) ~ UnsnocTF (a ': args)
  , BaseFunTF args
      (a -> BaseFunTF args
        (a -> b -> Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
                         (ProducerTF (c : b : a : args) (d -> e))
        ) -> Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
                      (ProducerTF (c : b : a : args) (d -> e))
      ) ~
      (l -> BaseFunTF initArgs
        (BaseFunTF args
          (a -> b -> Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
            (ProducerTF (c : b : a : args) (d -> e))
          ) -> Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
                     (ProducerTF (c : b : a : args) (d -> e))
        )
      )
  , BaseFunTF args
      (a -> Hyper (BaseFunTF args
        (a -> b -> Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
                         (ProducerTF (c : b : a : args) (d -> e))
        )) (Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
                     (ProducerTF (c : b : a : args) (d -> e))
           )
      ) ~
      (l -> BaseFunTF initArgs
        (Hyper (BaseFunTF args (a -> b -> Hyper
          (BaseFunTF args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
          (ProducerTF (c : b : a : args) (d -> e))))
          (Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
            (ProducerTF (c : b : a : args) (d -> e))
          )
        )
      )
  , BaseFunTF (Take1TF (DropLast2TF (b : a : args)))
      (xx
       -> BaseFunTF
            (Drop1TF (DropLast2TF (b : a : args)))
            ((l
              -> xx
              -> BaseFunTF
                   (DropLast2TF (b : a : args))
                   (Hyper
                      (BaseFunTF
                         args
                         (a
                          -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
                      (ProducerTF (c : b : a : args) (d -> e))))
             -> Hyper
                  (BaseFunTF
                     args
                     (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
                  (ProducerTF (c : b : a : args) (d -> e))))
    ~ (b
       -> BaseFunTF
            initArgs
            (BaseFunTF
               args
               (a
                -> b
                -> Hyper
                     (BaseFunTF
                        args
                        (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
                     (ProducerTF (c : b : a : args) (d -> e)))
             -> Hyper
                  (BaseFunTF
                     args
                     (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
                  (ProducerTF (c : b : a : args) (d -> e))))
  , ConstBaseFunc initArgs (a : args) (b -> c -> d -> e)
  , FoldComponents initArgs
      (BaseFunTF
         args
         (a
          -> b
          -> Hyper
               (BaseFunTF
                  args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
               (ProducerTF (c : b : a : args) (d -> e))))
      (Hyper
         (BaseFunTF
            args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
         (ProducerTF (c : b : a : args) (d -> e)))
  , FoldComponentB (DropLast2TF (b : a : args))
      xx
      (l
       -> xx
       -> BaseFunTF
            (DropLast2TF (b : a : args))
            (Hyper
               (BaseFunTF
                  args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
               (ProducerTF (c : b : a : args) (d -> e))))
      (Hyper
         (BaseFunTF
            args (a -> b -> c -> ProducerTF (c : b : a : args) (d -> e)))
         (ProducerTF (c : b : a : args) (d -> e)))
  , Produce fullFun (a : args) xx b c (d -> e)
  ) => Produce fullFun args xx a b (c -> d -> e) where
  produce f p
    = produce @fullFun @(a ': args) @xx @b @c @(d -> e) f
    . produceInter @args @xx @a @b @(c -> d -> e) p

zipWithN
  :: forall a b fun funTy.
    ( funTy ~ MarkResultTF fun
    , Produce (a -> b -> fun) '[] b a b funTy
    , ConstProducer '[] (a -> b -> funTy)
    )
  => (a -> b -> fun)
  -> ResultFunTF (a -> b -> funTy)
zipWithN f
  = produce @(a -> b -> fun) @'[] @b @a @b @funTy f
  . initProducer @(a -> b -> funTy) @a

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
