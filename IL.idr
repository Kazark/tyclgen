module IL

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
  | IsParameterizedOver (Maybe Nat)
