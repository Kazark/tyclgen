module Tr

import BoundAst
import Data.Fin
import Data.Vect
import Instances
import CodeGen

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

genVar : Nat -> String
genVar k =
  pack $ Stream.take (divNatNZ k 26 SIsNotZ + 1) $ repeat $ chr $ cast $ modNatNZ k 26 SIsNotZ + 97

genSRTPVar : Nat -> String
genSRTPVar k = "^" ++ genVar k

data LBranch = LeftBranch

parenthesize : String -> String
parenthesize s = "(" ++ s ++ ")"

maybeParenthesize : Maybe LBranch -> String -> String
maybeParenthesize = flip $ foldl $ flip $ \_ => parenthesize

parenthesizeVar : Nat -> String -> (Nat, String)
parenthesizeVar k s =
  (S k, parenthesize $ genVar k ++ " : " ++ s)

iAmIgnorant : Nat -> Maybe LBranch -> Monotype -> (Nat, String)
iAmIgnorant k _ (Term _) = (S k, genSRTPVar k)
iAmIgnorant k branch (FuncType x y) =
  let (k0, s0) = iAmIgnorant k (Just LeftBranch) x
      (k1, s1) = iAmIgnorant k0 Nothing y
  in (k1, maybeParenthesize branch $ s0 ++ " -> " ++ s1)
iAmIgnorant k _ (TypeFullyApplied x y) = (S k, genSRTPVar k)

halp : Nat -> Nat -> Maybe LBranch -> Monotype -> String
halp k v _ (FuncType x y) =
  let (k0, s0) = iAmIgnorant k Nothing x
      (v0, s1) = parenthesizeVar v s0
  in s1 ++ " " ++ halp k0 v0 Nothing y
halp k v Nothing m = ": " ++ (snd $ iAmIgnorant k Nothing m)
halp k v (Just x) m = snd $ parenthesizeVar v $ snd $ iAmIgnorant k Nothing m

test : String
test = halp Z Z Nothing $ uncurry FuncType TrimapType

data Sep = Comma | Star

record FSGenericType where
  constructor FSGenType
  pre : String
  sep : Sep
  targs : List String
  post : String

consTArg : String -> FSGenericType -> FSGenericType
consTArg targ (FSGenType pre sep targs post) = (FSGenType pre sep (targ :: targs) post)

data SameTypeCtr
  = SameTypeCtr' FSGenericType FSGenericType

doubleConsTArg : String -> SameTypeCtr -> SameTypeCtr
doubleConsTArg targ (SameTypeCtr' x y) = (SameTypeCtr' (consTArg targ x) (consTArg targ y))

genNSRTPVarsFrom : Nat -> Nat -> List String
genNSRTPVarsFrom n k = toList $ take n $ map genSRTPVar $ iterate S k

FSTupleType : List String -> FSGenericType
FSTupleType targs = FSGenType "( " Star targs ")"

FSRegularType : String -> List String -> FSGenericType
FSRegularType name targs = FSGenType (name ++ "< ") Comma targs ">"

FSArrayType : String -> FSGenericType
FSArrayType x = FSGenType "" Comma [x] "[]"

pairedGenericTArgs : Nat -> Nat -> (List String, List String)
pairedGenericTArgs n k =
  (genNSRTPVarsFrom (minus n k) k, genNSRTPVarsFrom (minus n k) (k + n))

sameTypeCtr_ : Nat -> MMTypeCtr n -> SameTypeCtr
sameTypeCtr_ k (Regular n x) =
  let (targs0, targs1) = pairedGenericTArgs (n + 1) k
  in SameTypeCtr' (FSRegularType x targs0) (FSRegularType x targs1)
sameTypeCtr_ k (Tuple n) =
  let (targs0, targs1) = pairedGenericTArgs (n + 2) k
  in SameTypeCtr' (FSTupleType targs0) (FSTupleType targs1)
sameTypeCtr_ _ Array = SameTypeCtr' (FSArrayType "^a") (FSArrayType "^b")
sameTypeCtr_ k (Appl1 x) = doubleConsTArg (genSRTPVar k) $ sameTypeCtr_ (S k) x

TODO : String
TODO = genSMI $ sameTypeCtrToSMI $ sameTypeCtr $ Appl1 $ Appl1 $ Tuple 2
-- BAD result:
--  "  static member inline SameTypeCtr (_ : ( ^a * ^b * ^c * ^d), _ : ( ^a * ^b * ^g * ^h)) : unit = ()" : String
-- Without breaking
-- genSMI $ sameTypeCtrToSMI $ sameTypeCtr $ Tuple Z
-- Which gives the good result
--  "  static member inline SameTypeCtr (_ : ( ^a * ^b), _ : ( ^c * ^d)) : unit = ()" : String
-- Also need to start thinking about: A, B, etc...

sameTypeCtr : MMTypeCtr n -> SameTypeCtr
sameTypeCtr = sameTypeCtr_ Z

genSep : Sep -> String
genSep Comma = ", "
genSep Star = " * "

concatWith : Sep -> List String -> String
concatWith sep = concat . intersperse (genSep sep)

genFsGenType : FSGenericType -> String
genFsGenType (FSGenType pre sep targs post) =
  pre ++ concatWith sep targs ++ post

sameTypeCtrToSMI : SameTypeCtr -> SMI
sameTypeCtrToSMI (SameTypeCtr' x y) =
  StatMethInli "SameTypeCtr" ["_ : " ++ genFsGenType x, "_ : " ++ genFsGenType y] "unit" "()"
