module Tr

import BoundAst
import Data.Fin
import Data.Vect
import Instances

%default total

-- We do not have the ability to actually express type signatures like
-- 
--     (a -> b) -> f a -> f b
-- 
-- in F#. However, we can fake it out with these methods, which have no runtime
-- use; they are purely a typelevel hack to let us have a way to predicate
-- truths about a type via member constraints.
-- 
-- The `SameTypeCtr` set of functions allow us to define the idea that for some
-- `^a0` and `^b0`, that they are `f a` and `f b`, in the sense that the `f` is
-- in fact the same type constructor, regardless of the types it is
-- parameterized over.
-- 
-- The `IsParameterizedOver*` set of functions allow us to define the idea that
-- for some `^a0` and `^a`, they are in fact `f a` and `a` such that `a` is in
-- fact the same type in both cases.
-- 
-- Ultimately, both are just getting around the fact that you can't
-- "peek inside" a statically resolved type parameter in F#.

--data HKTPred
--  = SameTypeCtr
--  | IsParameterizedOver

-- If a method's type uses TypeAppl, it will need to make sure to include ^hkt
-- in the generated F# code, for injecting HKTPreds.
--
-- For every pair of distinct TypeAppl with the same type constructor, one
-- SameTypeCtr will need to be scheduled to be generated.
-- For every unique TypeAppl, one IsParameterizedOverA will need to be
-- scheduled to be generated.
--
-- The generated code will always need a ^tc argument for every time class involved.
-- The generated code will need a SRTP for every monotype and typeappl in the equation.

||| Monotype reworked to be based on n-arry (uncurried) type applications and
||| function types rather than curried
data Monotype'
  = Term' String
  | FuncType' Monotype' (Monotype', List Monotype')
  | NAryTypeAppl' (List Monotype')

cons : a -> (a, List a) -> (a, List a)
cons x (x', xs) = (x, x' :: xs)

mutual -- Total this way, fascinatingly enough
  unwindUnaryTypeOp : UnaryTypeOp -> List Monotype'
  unwindUnaryTypeOp TypeclassCtr = []
  unwindUnaryTypeOp (NAryTypeAppl uto mt) = breakIntoSubExprs mt :: unwindUnaryTypeOp uto

  clingShangHoong : Monotype -> (Monotype', List Monotype')
  clingShangHoong (Term x) = (Term' x, [])
  clingShangHoong (FuncType x y) = cons (breakIntoSubExprs x) (clingShangHoong y)
  clingShangHoong (TypeFullyApplied x y) = (breakIntoSubExprs $ TypeFullyApplied x y, [])

  breakIntoSubExprs : Monotype -> Monotype'
  breakIntoSubExprs (Term x) = Term' x
  breakIntoSubExprs (FuncType x y) = FuncType' (breakIntoSubExprs x) $ clingShangHoong y
  breakIntoSubExprs (TypeFullyApplied uto mt) =
    NAryTypeAppl' $ reverse $ breakIntoSubExprs mt :: unwindUnaryTypeOp uto

genSRTPVar : Nat -> String
genSRTPVar k =
  pack $ Stream.take (divNatNZ k 26 SIsNotZ + 1) $ repeat $ chr $ cast $ modNatNZ k 26 SIsNotZ + 97

data LBranch = LeftBranch

maybeParenthesize : Maybe LBranch -> String -> String
maybeParenthesize branch s =
  foldl (\s => \_ => "(" ++ s ++ ")") s branch

mutual
  iAmIgnorant' : Nat -> UnaryTypeOp -> (Nat, String)
  iAmIgnorant' k TypeclassCtr = (S k, genSRTPVar k)
  iAmIgnorant' k (NAryTypeAppl x y) = (S k, genSRTPVar k)

  iAmIgnorant : Nat -> Maybe LBranch -> Monotype -> (Nat, String)
  iAmIgnorant k _ (Term _) = (S k, genSRTPVar k)
  iAmIgnorant k branch (FuncType x y) =
    let (k0, s0) = iAmIgnorant k (Just LeftBranch) x
        (k1, s1) = iAmIgnorant k0 Nothing y
    in (k1, maybeParenthesize branch $ s0 ++ " -> " ++ s1)
  iAmIgnorant k _ (TypeFullyApplied x y) = (S k, genSRTPVar k)

halp : Monotype -> (Nat, String)
halp = iAmIgnorant Z Nothing

test : String
test = snd $ halp $ uncurry FuncType TrimapType

data FSILTF : Nat -> Type where
  Term : Fin n -> FSILTF n
  Func : Fin n -> Fin n -> FSILTF n

data FSILType : (n : Nat) -> Type where
  FSILTy : FSILTF n -> Vect n Monotype' -> FSILType n

cardinality : Monotype' -> Nat
cardinality (Term' x) = ?cardinality_rhs_1
cardinality (FuncType' x y) = ?cardinality_rhs_2
cardinality (NAryTypeAppl' xs) = ?cardinality_rhs_3
