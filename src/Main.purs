module Main where

import Prelude (Unit)
--import Prelude (Unit, id, show, ($))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Unsafe.Coerce (unsafeCoerce)
import Data.Leibniz (type (~))
import Data.Either (Either(..))
--import Type.Row (kind RowList, Nil, Cons, class RowToList, class ListToRow)
import Data.Identity (Identity)
--import Data.Identity (Identity(..))
--import Data.Newtype (unwrap)
import Data.Tuple.Nested (type (/\))
import Type.Data.Boolean (class And, class Or, True, False, kind Boolean)


-- e.g: expand `f a ~ g b` to `f ~ g` and `a ~ b`
class ElabContext i o | i -> o
instance elabContextF
  :: ( ElabContext (@f ~ @g) o0
     , ElabContext (@a ~ @b) o1
     )
  => ElabContext (@(f a) ~ @(g b))
                 (o0 /\ o1)
else
instance elabContextEq
  :: ElabContext (@a ~ @b) (@a ~ @b)
else
instance elabContextAnd
  :: ( ElabContext l o0
     , ElabContext r o1
     )
  => ElabContext (l /\ r) (o0 /\ o1)


-- given an equality context `eq`, equate `i` and `o` but allow them to
-- differ by entries in the context
class Equate eq l r (out :: Boolean) | eq l r -> out
instance equateRefl
  :: Equate eq @a @a True
else
instance equateDiffSubst
  :: Equate (@a ~ @b) @a @b True
else
instance equateDiffSymm
  :: Equate (@b ~ @a) @a @b True
else
instance equateDiffAnd
  :: ( Equate l @a @b lo
     , Equate r @a @b ro
     , Or lo ro o
     )
  => Equate (l /\ r) @a @b o
else
instance equateF
  :: ( Equate eq @f @g lo
     , Equate eq @a @b ro
     , And lo ro o
     )
  => Equate eq @(f a) @(g b) o
else
instance equateNope
  :: Equate eq @a @b False



-- given an equality between `a` and `b`, structurally walk and equate `f` and
-- `g` but allow them to differ by `a` and `b` recursively in any parameter
class Substitute eq f g
instance substApp
  :: ( Substitute eq @i @o
     , Substitute eq @f @g
     )
  => Substitute eq @(f i) @(g o)
else
instance substTerm
  :: Equate eq @f @g True
  => Substitute eq @f @g

-- substitute without the proxies
class Substitute eq @f @g <= Subst eq f g
instance substInst
  :: Substitute eq @f @g
  => Subst eq f g

-- given an equality between `a` and `b` coerce an `f` into a `g` if they only
-- differ by occurrences of `a` and `b`
coerced :: forall eq ctx f g.
  ElabContext eq ctx =>
  Subst ctx f g =>
  eq -> f -> g
coerced _ f = unsafeCoerce f

infix 4 coerced as <~>


-- coercion example

example ::
  (@(Identity Int) ~ @(Array String)) /\ (@String ~ @Boolean) ->
  Either (Identity String) Int
example l = l <~> (Left [true] :: Either (Array Boolean) String)

example0 ::
  @(foo :: Int) ~ @(bar :: String) ->
  {bar :: String}
example0 l = l <~> {foo: 42}


{-
-- given a rowlist of cases for a fold
-- cull any that couldn't possibly be implemented
-- e.g: ( foo :: Int ~ String -> r
--      , bar :: Int ~ Int -> r )
-- should cull `foo` and keep `bar`

class CasesRL (i :: RowList)
              (o :: RowList)
              | i -> o
instance casesNil
  :: CasesRL Nil Nil
else
instance casesConsMatch
  :: CasesRL t o
  => CasesRL (Cons k (a ~ a -> r) t)
             (Cons k (a ~ a -> r) o)
else
instance casesConsDiff
  :: CasesRL t o
  => CasesRL (Cons k (a ~ b -> r) t)
             o
else
instance casesConsNeq
  :: CasesRL t o
  => CasesRL (Cons k r t)
             (Cons k r o)

class Cases (i :: # Type)
            (o :: # Type)
            | i -> o where
  cases :: Record o -> Record i

instance casesImpl
  :: ( RowToList i il
     , CasesRL il ol
     , ListToRow ol o
     )
  => Cases i o
  where
    cases = unsafeCoerce


-- gadt example

data Term t = Term (forall r.
  { int :: Int ~ t -> Int -> r Int
  , str :: String ~ t -> Term Int -> r String } ->
  r t)

-- smart constructors

int :: Int -> Term Int
int i = Term \o -> o.int id i

str :: Term Int -> Term String
str t = Term \o -> o.str id t

-- 'dumb' fold for a `Term`

runTerm :: forall r t.
  Term t ->
  { int :: Int ~ t -> Int -> r Int
  , str :: String ~ t -> Term Int -> r String } ->
  r t
runTerm (Term t) o = t o

type TermCases t r =
  ( int :: Int ~ t -> Int -> r Int
  , str :: String ~ t -> Term Int -> r String
  )

-- 'smart' fold for a `Term`
-- don't need to provide cases that are impossible

caseTerm :: forall r t c.
  Cases (TermCases t r) c =>
  Term t ->
  Record c ->
  r t
caseTerm t c = runTerm t dispatch
  where
    dispatch :: Record (TermCases t r)
    dispatch = cases c

goTerm :: forall t. Term t -> t
goTerm t = unwrap $ runTerm t
  { int: \_ -> Identity
  , str: \_ i -> Identity (show $ goTerm i)
  }

goTerm' :: Term String -> String
goTerm' t = unwrap $ caseTerm t
  { str: \_ i -> Identity (show $ goTerm i)
  }

goTerm'' :: Term Int -> Int
goTerm'' t = unwrap $ caseTerm t
  { int: \_ i -> Identity i
  }
-}

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  log "Hello sailor!"
