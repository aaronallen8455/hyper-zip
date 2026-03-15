{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
module HyperZip
  ( zipWithN
  ) where

import           Data.Kind
import           Control.Monad.Hyper

zipWithN
  :: forall a b fun funTy.
    ( funTy ~ MarkResultTF fun
    , Produce (a -> b -> fun) Nil b a b funTy
    , ConstProducer Nil (a -> b -> funTy)
    )
  => (a -> b -> fun)
  -> ResultFunTF (a -> b -> funTy)
zipWithN f
  = produce @(a -> b -> fun) @Nil @b @a @b @funTy f
  . initProducer @(a -> b -> funTy) @a

-- Used to represent type level lists as function types to optimize core simplification.
data Nil

-- Use function type as the arg rather than type lists?
type ProducerTF :: Type -> Type -> Type
type family ProducerTF args fun where
  ProducerTF args (y -> ResultTy res) = [res]
  ProducerTF args (x -> fun) =
    Hyper
      (BaseFunTF (x -> args) (ProducerTF (x -> args) fun))
      (ProducerTF (x -> args) fun)
  -- TODO: error case

type BaseFunTF :: Type -> Type -> Type
type family BaseFunTF args rest where
  BaseFunTF (x -> args) rest = BaseFunTF args (x -> rest)
  BaseFunTF Nil done = done

initProducer
  :: forall funTy firstArg funRest.
  ( ConstProducer Nil funTy
  , (firstArg -> funRest) ~ funTy
  , ProducerTF Nil funTy ~
      Hyper
        (BaseFunTF (firstArg -> Nil) (ProducerTF (firstArg -> Nil) funRest))
        (ProducerTF (firstArg -> Nil) funRest)
  )
  => [firstArg] -> ProducerTF Nil funTy
initProducer =
  foldr
    (\x -> push ($ x))
    (constProducer @Nil @funTy)

consumer
  :: forall args x y r fun initArgs l
   . ( '(initArgs, l) ~ UnsnocTF (x -> args)
     , fun ~ (l -> BaseFunTF initArgs (y -> r))
     , BaseFunTF args (x -> r) ~ (l -> BaseFunTF initArgs r)
     , Monoid (BaseFunTF args (x -> [r]))
     , ApplyArg (r -> y -> initArgs)
     , ConsResult (r -> y -> x -> args)
     )
  => fun -> ProducerTF args (x -> y -> ResultTy r) -> [y] -> [r]
consumer f p ys = invoke p $
  foldr
    (\y ->
      push $
        (consResult @(r -> y -> x -> args))
          (\l -> (applyArg @(r -> y -> initArgs)) (f l) y)
    )
    (k mempty)
    ys

class ConstProducer args funTy where
  constProducer :: ProducerTF args funTy

instance
  ConstProducer args (a -> b -> ResultTy res) where
  constProducer = k []

instance
  ConstProducer (a -> args) (b -> c -> d)
  => ConstProducer args (a -> b -> c -> d) where
  constProducer = k (constProducer @(a -> args) @(b -> c -> d))

k :: a -> Hyper b a
k = pure

data ResultTy (a :: Type)

type MarkResultTF :: Type -> Type
type family MarkResultTF funTy where
  MarkResultTF (a -> b) = a -> MarkResultTF b
  MarkResultTF a = ResultTy a

class ConstBaseFunc baseFunArgs args fun where
  constArgHyp :: BaseFunTF baseFunArgs (ProducerTF args fun)

instance ConstProducer args fun => ConstBaseFunc Nil args fun where
  constArgHyp = constProducer @args @fun

instance
  ( ConstBaseFunc initFunArgs args fun
  , '(initFunArgs, b) ~ UnsnocTF (a -> baseFunArgs)
  , BaseFunTF (a -> baseFunArgs) (ProducerTF args fun)
      ~ (b -> BaseFunTF initFunArgs (ProducerTF args fun))
  )
  => ConstBaseFunc (a -> baseFunArgs) args fun where
  constArgHyp = const (constArgHyp @initFunArgs @args @fun)

produceFinish
  :: forall args xx a b c d initArgs x.
    ( '(initArgs, x) ~ UnsnocTF (a -> args)
    , BaseFunTF (Take1TF (DropLast2TF (b -> a -> args)))
        (xx
         -> BaseFunTF
              (Drop1TF (DropLast2TF (b -> a -> args)))
              ((x -> xx -> BaseFunTF (DropLast2TF (b -> a -> args)) [d]) -> [d]))
      ~ (b -> BaseFunTF initArgs (BaseFunTF args (a -> b -> [d]) -> [d]))
    , BaseFunTF args (a -> BaseFunTF args (a -> b -> [d]) -> [d])
      ~ (x -> BaseFunTF initArgs (BaseFunTF args (a -> b -> [d]) -> [d]))
    , BaseFunTF args (a -> Hyper (BaseFunTF args (a -> b -> [d])) [d])
      ~ (x -> BaseFunTF initArgs (Hyper (BaseFunTF args (a -> b -> [d])) [d]))
    , ConstBaseFunc initArgs (a -> args) (b -> c -> ResultTy d)
    , ArgShift (DropLast2TF (b -> a -> args)) xx
        (x -> xx -> BaseFunTF (DropLast2TF (b -> a -> args)) [d])
        [d]
    , PushArgFun initArgs (BaseFunTF args (a -> b -> [d])) [d]
    )
  => ProducerTF args (a -> b -> c -> ResultTy d)
  -> [b]
  -> ProducerTF (a -> args) (b -> c -> ResultTy d)
produceFinish p bs = invoke p $
    foldr
      (\b ->
        push
          ( (pushArgFun @(a -> args) @(BaseFunTF args (a -> b -> [d])) @[d])
            (\x -> argShift @(DropLast2TF (b -> a -> args)) @xx @_ @(ProducerTF (b -> a -> args) (c -> ResultTy d))
              (\xx f -> f x xx) b
            )
          )
        )
      (k (constArgHyp @(a -> args) @(a -> args) @(b -> c -> ResultTy d)))
      bs

produceInter
  :: forall args xx x y fun initArgs l.
    ( '(initArgs, l) ~ UnsnocTF (x -> args)
    , BaseFunTF args (x -> ProducerTF (x -> args) (y -> fun))
        ~ (l -> BaseFunTF initArgs (ProducerTF (x -> args) (y -> fun)))
    , ConstBaseFunc initArgs (x -> args) (y -> fun)
    , BaseFunTF args
        (x -> BaseFunTF args
                (x -> y -> ProducerTF (y -> x -> args) fun)
                -> ProducerTF (y -> x -> args) fun
        ) ~ (l -> BaseFunTF initArgs
                    (BaseFunTF args (x -> y -> ProducerTF (y -> x -> args) fun)
                    -> ProducerTF (y -> x -> args) fun))
    , BaseFunTF args
        (x -> Hyper (BaseFunTF args (x -> y -> ProducerTF (y -> x -> args) fun))
                    (ProducerTF (y -> x -> args) fun)
        ) ~ (l -> BaseFunTF initArgs
                    (Hyper (BaseFunTF args (x -> y -> ProducerTF (y -> x -> args) fun))
                           (ProducerTF (y -> x -> args) fun)
                    )
            )
    , ProducerTF (x -> args) (y -> fun)
        ~ Hyper (BaseFunTF args (x -> y -> ProducerTF (y -> x -> args) fun))
                (ProducerTF (y -> x -> args) fun)
    , PushArgFun
        initArgs
        (BaseFunTF args (x -> y -> ProducerTF (y -> x -> args) fun))
        (ProducerTF (y -> x -> args) fun)
    , BaseFunTF (Take1TF (DropLast2TF (y -> x -> args)))
        (xx
         -> BaseFunTF
              (Drop1TF (DropLast2TF (y -> x -> args)))
              ((l
                -> xx
                -> BaseFunTF
                     (DropLast2TF (y -> x -> args)) (ProducerTF (y -> x -> args) fun))
               -> ProducerTF (y -> x -> args) fun))
      ~ (y
         -> BaseFunTF
              initArgs
              (BaseFunTF args (x -> y -> ProducerTF (y -> x -> args) fun)
               -> ProducerTF (y -> x -> args) fun))
    , ArgShift
        (DropLast2TF (y -> x -> args))
        xx
        (l -> xx -> BaseFunTF (DropLast2TF (y -> x -> args)) (ProducerTF (y -> x -> args) fun))
        (ProducerTF (y -> x -> args) fun)
    )
  => ProducerTF args (x -> y -> fun)
  -> [y]
  -> ProducerTF (x -> args) (y -> fun)
produceInter p ys = invoke p $
  foldr
    (\y ->
      push
        (
          (pushArgFun @(x -> args) @_ @(ProducerTF (y -> x -> args) fun))
            (\l -> argShift @(DropLast2TF (y -> x -> args)) @xx @_ @(ProducerTF (y -> x -> args) fun)
              (\xx f -> f l xx) y
            )
        )
    )
    (k (constArgHyp @(x -> args) @(x -> args) @(y -> fun)))
    ys

type family DropLast2TF args where
  DropLast2TF (a -> b -> Nil) = Nil
  DropLast2TF (x -> xs) = x -> DropLast2TF xs

-- args in reverse order, e.g. [e,d,c,b,a]
type family ConsResultTF args where
  ConsResultTF (resTy -> _ -> args) =
    BaseFunTF args resTy -> [resTy] -> BaseFunTF args [resTy]

type family ApplyArgTF args where
  ApplyArgTF (resTy -> pen -> args) =
    BaseFunTF (pen -> args) resTy -> pen -> BaseFunTF args resTy

class ConsResult args where
  consResult :: ConsResultTF args

instance ConsResult (a -> b -> c -> Nil) where
  consResult f xs c = f c : xs

instance
  ( '(restInit, x) ~ UnsnocTF (d -> rest)
  , BaseFunTF rest (d -> c -> a)
    ~ (x -> BaseFunTF restInit (c -> a))
  , BaseFunTF rest (d -> c -> [a])
    ~ (x -> BaseFunTF restInit (c -> [a]))
  , ConsResult (a -> b -> c -> restInit)
  ) => ConsResult (a -> b -> c -> d -> rest) where
  consResult f res x = consResult @(a -> b -> c -> restInit) (f x) res

class ApplyArg args where
  applyArg :: ApplyArgTF args

instance ApplyArg (a -> b -> Nil) where
  applyArg = id

instance
  ( '(restInit, x) ~ UnsnocTF (c -> rest)
  , BaseFunTF rest (c -> a)
    ~ (x -> BaseFunTF restInit a)
  , BaseFunTF rest (c -> b -> a)
    ~ (x -> BaseFunTF restInit (b -> a))
  , ApplyArg (a -> b -> restInit)
  ) => ApplyArg (a -> b -> c -> rest) where
  applyArg f b x = applyArg @(a -> b -> restInit) (f x) b

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
  ( '(initArgs, l) ~ UnsnocTF (a -> args)
  , fullFun ~ (l -> BaseFunTF initArgs (b -> c))
  , BaseFunTF args (a -> c) ~ (l -> BaseFunTF initArgs c)
  , Monoid (BaseFunTF args (a -> [c]))
  , ApplyArg (c -> b -> initArgs)
  , ConsResult (c -> b -> a -> args)
  )
  => Produce fullFun args xx a b (ResultTy c) where
  produce = consumer @args @a @b @c @fullFun @initArgs @l

instance
  ( '(initArgs, l) ~ UnsnocTF (a -> args)
  , BaseFunTF args (a -> Hyper (BaseFunTF args (a -> b -> [d])) [d])
      ~ (l -> BaseFunTF initArgs (Hyper (BaseFunTF args (a -> b -> [d])) [d]))
  , Produce fullFun (a -> args) xx b c (ResultTy d)
  , BaseFunTF args (a -> BaseFunTF args (a -> b -> [d]) -> [d])
      ~ (l -> BaseFunTF initArgs (BaseFunTF args (a -> b -> [d]) -> [d]))
  , BaseFunTF (Take1TF (DropLast2TF (b -> a -> args)))
      (xx -> BaseFunTF (Drop1TF (DropLast2TF (b -> a -> args)))
               ((l -> xx -> BaseFunTF (DropLast2TF (b -> a -> args)) [d]) -> [d]))
      ~ (b -> BaseFunTF initArgs (BaseFunTF args (a -> b -> [d]) -> [d]))
  , ConstBaseFunc initArgs (a -> args) (b -> c -> ResultTy d)
  , ArgShift
      (DropLast2TF (b -> a -> args))
      xx
      (l -> xx -> BaseFunTF (DropLast2TF (b -> a -> args)) [d])
      [d]
  , PushArgFun initArgs (BaseFunTF args (a -> b -> [d])) [d]
  )
  => Produce fullFun args xx a b (c -> ResultTy d) where
  produce f p
    = produce @fullFun @(a -> args) @xx @b @c @(ResultTy d) f
    . produceFinish @args @xx @a @b @c @d @initArgs @l p

instance
  ( '(initArgs, l) ~ UnsnocTF (a -> args)
  , BaseFunTF args
      (a -> BaseFunTF args
        (a -> b -> Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
                         (ProducerTF (c -> b -> a -> args) (d -> e))
        ) -> Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
                      (ProducerTF (c -> b -> a -> args) (d -> e))
      ) ~
      (l -> BaseFunTF initArgs
        (BaseFunTF args
          (a -> b -> Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
            (ProducerTF (c -> b -> a -> args) (d -> e))
          ) -> Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
                     (ProducerTF (c -> b -> a -> args) (d -> e))
        )
      )
  , BaseFunTF args
      (a -> Hyper (BaseFunTF args
        (a -> b -> Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
                         (ProducerTF (c -> b -> a -> args) (d -> e))
        )) (Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
                     (ProducerTF (c -> b -> a -> args) (d -> e))
           )
      ) ~
      (l -> BaseFunTF initArgs
        (Hyper (BaseFunTF args (a -> b -> Hyper
          (BaseFunTF args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
          (ProducerTF (c -> b -> a -> args) (d -> e))))
          (Hyper (BaseFunTF args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
            (ProducerTF (c -> b -> a -> args) (d -> e))
          )
        )
      )
  , BaseFunTF (Take1TF (DropLast2TF (b -> a -> args)))
      (xx
       -> BaseFunTF
            (Drop1TF (DropLast2TF (b -> a -> args)))
            ((l
              -> xx
              -> BaseFunTF
                   (DropLast2TF (b -> a -> args))
                   (Hyper
                      (BaseFunTF
                         args
                         (a
                          -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
                      (ProducerTF (c -> b -> a -> args) (d -> e))))
             -> Hyper
                  (BaseFunTF
                     args
                     (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
                  (ProducerTF (c -> b -> a -> args) (d -> e))))
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
                        (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
                     (ProducerTF (c -> b -> a -> args) (d -> e)))
             -> Hyper
                  (BaseFunTF
                     args
                     (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
                  (ProducerTF (c -> b -> a -> args) (d -> e))))
  , ConstBaseFunc initArgs (a -> args) (b -> c -> d -> e)
  , PushArgFun initArgs
      (BaseFunTF
         args
         (a
          -> b
          -> Hyper
               (BaseFunTF
                  args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
               (ProducerTF (c -> b -> a -> args) (d -> e))))
      (Hyper
         (BaseFunTF
            args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
         (ProducerTF (c -> b -> a -> args) (d -> e)))
  , ArgShift (DropLast2TF (b -> a -> args))
      xx
      (l
       -> xx
       -> BaseFunTF
            (DropLast2TF (b -> a -> args))
            (Hyper
               (BaseFunTF
                  args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
               (ProducerTF (c -> b -> a -> args) (d -> e))))
      (Hyper
         (BaseFunTF
            args (a -> b -> c -> ProducerTF (c -> b -> a -> args) (d -> e)))
         (ProducerTF (c -> b -> a -> args) (d -> e)))
  , Produce fullFun (a -> args) xx b c (d -> e)
  ) => Produce fullFun args xx a b (c -> d -> e) where
  produce f p
    = produce @fullFun @(a -> args) @xx @b @c @(d -> e) f
    . produceInter @args @xx @a @b @(c -> d -> e) p

type family PushArgFunTF args h1 h2 where
  PushArgFunTF args h1 h2 =
    BaseFunTF args
         ( h1 -> h2)
    -> Hyper h1 h2
    -> BaseFunTF args (Hyper h1 h2)

type family ArgShiftTF args t1 h1 h2 where
  ArgShiftTF args t1 h1 h2 =
    ( t1
      -> h1
      -> BaseFunTF args h2)
    -> BaseFunTF (Take1TF args)
        ( t1 -> BaseFunTF (Drop1TF args) (h1 -> h2))

type family Take1TF args where
  Take1TF (a -> args) = (a -> Nil)
  Take1TF Nil = Nil

type family Drop1TF args where
  Drop1TF (a -> args) = args
  Drop1TF Nil = Nil

class PushArgFun args h1 h2 where
  pushArgFun :: PushArgFunTF args h1 h2

instance PushArgFun Nil h1 h2 where
  pushArgFun = push

instance
    ( '(argsInit, a) ~ UnsnocTF (x -> args)
    , PushArgFun argsInit h1 h2
    , BaseFunTF (x -> args) (h1 -> h2) ~ (a -> BaseFunTF argsInit (h1 -> h2))
    , BaseFunTF (x -> args) (Hyper h1 h2) ~ (a -> BaseFunTF argsInit (Hyper h1 h2))
    )
  => PushArgFun (x -> args) h1 h2 where
  pushArgFun f h (a :: a) = (pushArgFun @argsInit @h1 @h2) (f a) h

class ArgShift args t1 h1 h2 where
  argShift :: ArgShiftTF args t1 h1 h2

instance ArgShift Nil x h1 h2 where
  argShift = id

instance
  ( '(argsInit, a) ~ UnsnocTF (x -> args)
  , ArgShift argsInit a h1 h2
  , BaseFunTF (Take1TF argsInit) (a -> BaseFunTF (Drop1TF argsInit) (h1 -> h2))
      ~ (x -> BaseFunTF args (h1 -> h2))
  , BaseFunTF args (x -> h2)
      ~ (a -> BaseFunTF argsInit h2)
  )
  => ArgShift (x -> args) y h1 h2 where
  argShift f x y = argShift @argsInit @a @h1 @h2 (flip $ f y) x

type UnsnocTF :: Type -> (Type, Type)
type family UnsnocTF xs where
  UnsnocTF (x -> Nil) = '(Nil, x)
  UnsnocTF (x -> xs) = ConsFstTF x (UnsnocTF xs)

type ConsFstTF :: Type -> (Type, Type) -> (Type, Type)
type family ConsFstTF x t where
  ConsFstTF x '(acc, r) = '(x -> acc, r)
