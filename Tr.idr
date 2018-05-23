module Tr

import BoundAst

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

data HKTPred
  = SameTypeCtr
  | IsParameterizedOver

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

hktPredsAboutMonotype : Monotype -> List (List String)
hktPredsAboutMonotype (Term _) = []
hktPredsAboutMonotype (FuncType x y) = hktPredsAboutMonotype x ++ hktPredsAboutMonotype y
hktPredsAboutMonotype (NullaryTypeAppl TypeclassCtr tcc) = hktPredsAboutMonotype tcc
hktPredsAboutMonotype (NullaryTypeAppl (NAryTypeAppl x z) y) = ?truthsAbout_rhs_2

tcRequiresPreds : Typeclass n msigs -> List HKTPred
tcRequiresPreds (TyCl _) = ?deduceHKTPred_rhs_1
