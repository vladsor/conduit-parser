{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}

{-|
Module      : Data.Conduit.Parser
Description : Short description
Copyright   : (c) Vladimir Sorokin, 2014-2015
License     : BSD3
Maintainer  : v.d.sorokin@gmail.com
Stability   : experimental
Portability : portable

Simple combinator library for parsing generic values and wrap it in conduit.
-}
module Data.Conduit.Parser
  ( Parser
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
#ifdef GHC_INTERACTIVE
import Data.Conduit.List
#endif
import Data.Sequence (Seq, (<|))
import qualified Data.Sequence as Seq
import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Monoid
import Data.Maybe

-- | The result of a parse.  This is parameterised over the type @i@
-- of string that was processed.
--
-- This type is an instance of 'Functor', where 'fmap' transforms the
-- value in a 'Done' result.
data IResult e i r = Fail !e
                   | Partial !Bool !(Maybe i -> IResult e i r)
                   | Done !r

instance Functor (IResult e i) where
  fmap f (Done o) = Done (f o)
  fmap _ (Fail e) = Fail e
  fmap f (Partial u g) = Partial u (fmap f . g)

-- | The core parser type.  This is parameterised over the type @i@ of
-- string being processed.
--
-- This type is an instance of the following classes:
--
-- * 'Monad'
--
-- * 'Functor' and 'Applicative', which follow the usual definitions.
newtype Parser e i a = Parser {
    runParser :: forall r. Maybe i -> Failure e i r -> Success e i a r -> IResult e i r
  }

type Failure e i   r = e -> Bool -> IResult e i r
type Success e i a r = a -> Bool -> IResult e i r

instance Functor (Parser e i) where
  fmap g p = Parser $ \i f s -> runParser p i f (s . g)

-- | The parser p <?> msg behaves as parser p, but whenever the parser p fails without consuming any input, it replaces expect error messages with the expect error message msg.
(<?>) :: (Monoid (m e), Applicative m) => Parser (m e) i a -> e -> Parser (m e) i a
p <?> e = Parser $ \i f s -> runParser p i (f . mappend (pure e)) s

returnP :: o -> Parser e i o
returnP a = Parser $ \_ _ s -> s a False

failP :: Monoid e => Parser e i o
failP = Parser $ \_ f _ -> f mempty False

instance Applicative (Parser e i) where
  pure = returnP
  f <*> v = do
      f1 <- f
      v1 <- v
      return $ f1 v1

instance Monad (Parser e i) where
  return = returnP
  p >>= pf = Parser $ \i f s -> runParser p i f $ \a u -> Partial u $ \i' -> runParser (pf a) i' f s

forceParser :: Parser e i a -> Maybe i -> Failure e i r -> Success e i a r -> IResult e i r
forceParser p i  = (go . ) . runParser p i
  where
    go (Partial False pf) = go (pf i)
    go r = r

pplus :: Parser e i o -> Parser e i o -> Parser e i o
pplus p1 p2 =
    Parser $ \i f s ->
        case (forceParser p1 i f s, forceParser p2 i f s) of
            (Done o, _) -> Done o
            (Fail e, Fail _) -> Fail e
            (_, Done o) -> Done o
            (Partial u pf, _) -> Partial u pf
            (_, Partial u pf) -> Partial u pf

instance Monoid e => Alternative (Parser e i) where
  empty = failP
  a <|> b = pplus a b

instance Monoid e => MonadPlus (Parser e i) where
  mzero = failP
  mplus = pplus

-- | Converting Parser to conduit sink
sinkParse :: (Monad m, Monoid e)
          => Parser e i o -- ^ Converted parser
          -> Sink i m (Either (Maybe i, e) o)
sinkParse p = await >>= \i -> go (runParser p i (const . Fail) (const . Done)) i
    where
        go (Fail e) i = return $ Left (i, e)
        go (Done o) _ = return $ Right o
        go (Partial False f) i = go (f i) i
        go (Partial True f) _ = await >>= \i' -> go (f i') i'

-- | The parser satisfy g succeeds for any input for which the supplied function g returns True. Returns the input that is actually parsed.
satisfy :: (Monoid e)
        => (i -> Bool) -- ^ function for testing input
        -> Parser e i i
satisfy g = Parser $ \ i f s -> fromMaybe (f mempty False) $ flip fmap i $ \i' -> if g i' then s i' True else f mempty False

-- | The parser succeeds if function return Just value
extract :: Monoid e
        => (i -> Maybe o) -- ^ function for translate input
        -> Parser e i o
extract g = Parser $ \i f s -> maybe (f mempty False) (`s` True) . join $ fmap g i

-- | This parser succeeds for any input. Returns the parsed input.
any :: Monoid e => Parser e i i
any = Parser $ \ i f s -> maybe (f mempty False) (`s` True) i

-- | This parser only succeeds at the end of the input.
eos :: Monoid e => Parser e i ()
eos = Parser $ \ i f s -> if isNothing i then s () False else f mempty False

-- | some p applies the parser p one or more times. Returns a Data.Sequence of the returned values of p.
some :: Monoid e => Parser e i o -> Parser e i (Seq o)
some p = (<|) <$> p <*> many p

-- | many p applies the parser p zero or more times. Returns a Data.Sequence of the returned values of p.
many :: Monoid e => Parser e i o -> Parser e i (Seq o)
many p = pure Seq.empty <|> some p

-- | some' p applies the parser p one or more times (greedy version). Returns a Data.Sequence of the returned values of p.
some' :: Monoid e => Parser e i o -> Parser e i (Seq o)
some' p = (<|) <$> p <*> many' p

-- | many' p applies the parser p one or more times (greedy version). Returns a Data.Sequence of the returned values of p.
many' :: Monoid e => Parser e i o -> Parser e i (Seq o)
many' p = some' p <|> pure Seq.empty

-- | folds input stream with parser one or more times.
someF :: Monoid e
      => a -- ^ accumulator
     -> (a -> Parser e i a) -- ^ folding function
     -> Parser e i a
someF v f = f v >>= flip manyF f

-- | folds input stream with parser zero or more times.
manyF :: Monoid e
      => a -- ^ accumulator
      -> (a -> Parser e i a) -- ^ folding function
      -> Parser e i a
manyF v f = pure v <|> someF v f

-- | folds input stream with parser one or more times (greedy version).
someF' :: Monoid e
       => a -- ^ accumulator
       -> (a -> Parser e i a) -- ^ folding function
       -> Parser e i a
someF' v f = f v >>= flip manyF' f

-- | folds input stream with parser zero or more times (greedy version).
manyF' :: Monoid e
       => a -- ^ accumulator
       -> (a -> Parser e i a) -- ^ folding function
       -> Parser e i a
manyF' v f = someF' v f <|> pure v


#ifdef GHC_INTERACTIVE
str = "abbabbbabaac"
ab :: Parser [String] Char (Char, Seq Char)
ab = do
  a <- (satisfy (== 'a') <?> "expected a")
  b <- many (satisfy (== 'b') <?> "expected b")
  return (a,b)
ps1 :: Parser [String] Char (Seq (Char, Seq Char), Char)
ps1 = do
      a <- many ab
      c <- satisfy (== 'c') <?> "expected c"
      return (a, c)
ps2 :: Parser [String] Char Char
ps2 = (satisfy (== 'a') <?> "expected a") <|> (satisfy (== 'c') <?> "expected c")

ps3 :: Parser [String] Char Char
ps3 = many any >> (satisfy (== 'c') <?> "expected c")
#endif
