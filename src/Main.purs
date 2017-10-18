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
import Type.Data.Boolean (class Or, True, False, kind Boolean)


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

foreign import kind List
foreign import data Nl :: List
foreign import data Cn :: Type -> List -> List

class EquivTo (all :: Type)
              (eq :: Type)
              (seen :: List)
              (a :: Type)
              (b :: Type)
              (out :: Boolean)
              | all eq seen a b -> out
instance equivToLeibLeft
  :: Equate all all s @a @x out
  => EquivTo all (@b ~ @x) s @a @b out
else
instance equivToLeibRight
  :: Equate all all s @a @x out
  => EquivTo all (@x ~ @b) s @a @b out
else
instance equivToLeibOther
  :: EquivTo all (@a ~ @b) s @i @o False
else
instance equivToAnd
  :: ( EquivTo all l s @a @b lout
     , EquivTo all r s @a @b rout
     , Or lout rout out
     )
  => EquivTo all (l /\ r) s @a @b out

class Seen (ctx :: List)
           t
           (out :: Boolean)
           | ctx t -> out
instance seenNl
  :: Seen Nl @typ False
else
instance seenCnY
  :: Seen (Cn @typ tl) @typ True
else
instance seenCnR
  :: Seen tl @typ out
  => Seen (Cn @hd tl) @typ out


-- given an equality context `eq`, equate `i` and `o` but allow them to
-- differ by entries in the context
class Equate all eq (seen :: List) l r (out :: Boolean) | eq seen l r -> out
instance equateRefl
  :: Equate all eq s @a @a True
else
instance equateDiffSubst
  :: Equate all (@a ~ @b) s @a @b True
else
instance equateDiffSymm
  :: Equate all (@b ~ @a) s @a @b True
else
instance equateElse
  :: ( Seen s @b isSeen
     , EquateIfNotSeen isSeen all eq s @a @b o
     )
  => Equate all eq s @a @b o
else
instance equateDiffAnd
  :: ( Equate all l s @a @b lo
     , Equate all r s @a @b ro
     , Or lo ro o
     )
  => Equate all (l /\ r) s @a @b o
else
instance equateNope
  :: Equate all eq s @a @b False

class EquateIfNotSeen (isSeen :: Boolean)
                      all
                      eq
                      (seen :: List)
                      l
                      r
                      (out :: Boolean)
                      | isSeen all eq seen l r -> out
instance equateIfNotSeenFalse
  :: EquivTo all eq (Cn @b s) @a @b out
  => EquateIfNotSeen False all eq s @a @b out
else
instance equateIfNotSeenTrue
  :: EquateIfNotSeen True all eq s @a @b False

-- given an equality between `a` and `b`, structurally walk and equate `f` and
-- `g` but allow them to differ by `a` and `b` recursively in any parameter
class Substitute eq f g
instance substApp
  :: ( Substitute eq @f @g
     , Substitute eq @i @o
     )
  => Substitute eq @(f i) @(g o)
else
instance substTerm
  :: Equate eq eq Nl @f @g True
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

infix 4 coerced as ~$


-- coercion example

example ::
  (@(Identity Int) ~ @(Array String)) /\ (@String ~ @Boolean) ->
  Either (Identity Int) Int
example l = l ~$ (Left [true] :: Either (Array Boolean) String)


example' :: forall a b c d e.
  (@a ~ @b) /\
  (@c ~ @b) /\
  (@d ~ @b) /\
  (@c ~ @e) /\
  (@e ~ @d) ->
  a -> e
example' l a = l ~$ a
  


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
