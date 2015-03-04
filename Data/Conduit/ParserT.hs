{-# LANGUAGE RankNTypes #-}

{-|
Module      : Data.Conduit.ParserT
Description : Short description
Copyright   : (c) Vladimir Sorokin, 2015
License     : BSD3
Maintainer  : v.d.sorokin@gmail.com
Stability   : experimental
Portability : portable

Here is a longer description of this module, containing some
commentary with @some markup@.
-}
module Data.Conduit.ParserT
  ( ParserT
  , (<?>)
  , sinkParse
  , satisfy
  , extract
  , many
  , some
  , many'
  , some'
  , manyF
  , someF
  , manyF'
  , someF'
  , any
  , eos
  ) where

import Prelude hiding (any)
import Data.Conduit
import Data.Sequence (Seq, (<|))
import qualified Data.Sequence as Seq
import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Monoid
import Data.Maybe
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Conditional (ifM)

-- | The result of a parse.  This is parameterised over the type @i@
-- of string that was processed.
--
-- This type is an instance of 'Functor', where 'fmap' transforms the
-- value in a 'Done' result.
data IResult e i m r = Fail e
                     | Partial !Bool !(Maybe i -> m (IResult e i m r))
                     | Done r

--instance MonadTrans (IResult e i) where
--  lift m = Done m

instance Monad m => Functor (IResult e i m) where
  fmap f (Done o) = Done (f o)
  fmap _ (Fail e) = Fail e
  fmap f (Partial u g) = Partial u (liftM (fmap f) . g)

-- | The core parser type.  This is parameterised over the type @i@ of
-- string being processed.
--
-- This type is an instance of the following classes:
--
-- * 'Monad'
--
-- * 'Functor' and 'Applicative', which follow the usual definitions.
newtype ParserT e i m a = ParserT {
    runParserT :: forall r. Maybe i -> Failure e i m r -> Success e i a m r -> m (IResult e i m r)
  }

type Failure e i   m r = e -> Bool -> m (IResult e i m r)
type Success e i a m r = a -> Bool -> m (IResult e i m r)

instance Functor (ParserT e i m) where
  fmap g p = ParserT $ \i f s -> runParserT p i f (s . g)

(<?>) :: (Monoid (f e), Applicative f) => ParserT (f e) i m a -> e -> ParserT (f e) i m a
p <?> e = ParserT $ \i f s -> runParserT p i (f . mappend (pure e)) s

returnP :: o -> ParserT e i m o
returnP a = ParserT $ \_ _ s -> s a False

failP :: Monoid e => ParserT e i m o
failP = ParserT $ \_ f _ -> f mempty False

bindP :: Monad m => ParserT e i m a -> (a -> ParserT e i m o) -> ParserT e i m o
bindP p pf = ParserT $ \i f s -> runParserT p i f $ \a u -> return $ Partial u $ \i' -> runParserT (pf a) i' f s

instance Monad m => Applicative (ParserT e i m) where
  pure = returnP
  f <*> v = do
      f1 <- f
      v1 <- v
      return $ f1 v1

instance Monad m => Monad (ParserT e i m) where
  return = returnP
  p >>= pf = bindP p pf

forceParserT :: Monad m => ParserT e i m a -> Maybe i -> Failure e i m r -> Success e i a m r -> m (IResult e i m r)
forceParserT p i f s = go =<< runParserT p i f s
  where
    go (Partial False pf) = pf i >>= go
    go r = return r

pplus :: Monad m => ParserT e i m o -> ParserT e i m o -> ParserT e i m o
pplus p1 p2 =
    ParserT $ \i f s -> do
      r1 <- forceParserT p1 i f s
      case r1 of
        Done o -> return $ Done o
        _ -> do
          r2 <- forceParserT p2 i f s
          return $ case r2 of
            Fail _ ->  r1
            Done o -> Done o
            Partial u pf -> case r1 of
              Partial _ _ -> r1
              _ -> r2

instance (Monoid e, Monad m) => Alternative (ParserT e i m) where
  empty = failP
  a <|> b = pplus a b

instance (Monoid e, Monad m) => MonadPlus (ParserT e i m) where
  mzero = failP
  mplus = pplus

instance MonadTrans (ParserT e i) where
  lift m = ParserT $ \_ _ s -> (m >>= flip s False)

sinkParse :: (Monad m, Monoid e) => ParserT e i m o -> Sink i m (Either (Maybe i, e) o)
sinkParse p = await >>= \i -> lift (runParserT p i (\e _ -> return $ Fail e) (\r _ -> return $ Done r)) >>= \r -> go r i
    where
        go (Fail e) i = return $ (Left . (,) i) e
        go (Done o) _ = return $ Right o
        go (Partial False f) i = lift (f i) >>= \r -> go r i
        go (Partial True f) _ = await >>= \i' -> lift (f i') >>= \r -> go r i'

satisfy :: (Monoid e) => (i -> Bool) -> ParserT e i m i
satisfy g = ParserT $ \ i f s -> fromMaybe (f mempty False) $ flip fmap i $ \i' -> if g i' then s i' True else f mempty False

satisfyM :: (Monoid e, Monad m) => (i -> m Bool) -> ParserT e i m i
satisfyM g = ParserT $ \ i f s -> fromMaybe (f mempty False) $ flip fmap i $ \i' -> ifM (g i') (s i' True) (f mempty False)

extract :: Monoid e => (i -> Maybe o) -> ParserT e i m o
extract g = ParserT $ \i f s -> maybe (f mempty False) (`s` True) . join $ fmap g i

extractM :: (Monoid e, Monad m) => (i -> m (Maybe o)) -> ParserT e i m o
extractM g = ParserT $ \i f s -> maybe (f mempty False) (`s` True) =<< maybe (return Nothing) g i

any :: Monoid e => ParserT e i m i
any = ParserT $ \ i f s -> maybe (f mempty False) (`s` True) i

eos :: Monoid e => ParserT e i m ()
eos = ParserT $ \ i f s -> if isNothing i then s () False else f mempty False

-- | many p applies the parser p one or more times. Returns a Data.Sequence of the returned values of p.
some :: (Monoid e, Monad m) => ParserT e i m o -> ParserT e i m (Seq o)
some p = (<|) <$> p <*> many p

-- | many p applies the parser p zero or more times. Returns a Data.Sequence of the returned values of p.
many :: (Monoid e, Monad m) => ParserT e i m o -> ParserT e i m (Seq o)
many p = pure Seq.empty <|> some p

-- | many p applies the parser p one or more times. Returns a Data.Sequence of the returned values of p.
some' :: (Monoid e, Monad m) => ParserT e i m o -> ParserT e i m (Seq o)
some' p = (<|) <$> p <*> many' p

-- | many p applies the parser p one or more times. Returns a Data.Sequence of the returned values of p.
many' :: (Monoid e, Monad m) => ParserT e i m o -> ParserT e i m (Seq o)
many' p = some' p <|> pure Seq.empty

someF :: (Monoid e, Monad m) => a -> (a ->  ParserT e i m a) -> ParserT e i m a
someF v f = f v >>= flip manyF f

manyF :: (Monoid e, Monad m) => a -> (a ->  ParserT e i m a) -> ParserT e i m a
manyF v f = pure v <|> someF v f

someF' :: (Monoid e, Monad m) => a -> (a ->  ParserT e i m a) -> ParserT e i m a
someF' v f = f v >>= flip manyF' f

manyF' :: (Monoid e, Monad m) => a -> (a ->  ParserT e i m a) -> ParserT e i m a
manyF' v f = someF' v f <|> pure v
