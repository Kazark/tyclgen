module Main

%default total

mutual
  ||| An unary type operator is a type of kind * -> *
  data UnaryTypeOp
    = TypeCtr String
    | NAryTypeAppl (UnaryTypeOp, Monotype)

  ||| A monotype is a type of kind *
  data Monotype
    = Term String
    | FuncType (Monotype, Monotype)
    | NullaryTypeAppl (UnaryTypeOp, Monotype)

data MethodImpl = MethodImpl' String
data Method = Method' ((Monotype, Monotype), MethodImpl)

||| Monomorphic type constructors
||| (S n) is the arity of the type constructor
data MMTypeCtr : (n : Nat) -> Type where
  Regular : (n: Nat) -> String -> MMTypeCtr n
  Tuple   : MMTypeCtr n
  Array   : MMTypeCtr Z

||| (S n) is the arity of the typeclass
record Typeclass (n : Nat) where
  constructor TyCl
  name : String
  ||| These are the methods that will be used to implement the others. You
  ||| might also call them abstract or pure virtual in OO terminology.
  abstractMethods : List (Monotype, Monotype)

||| TODO Need number of methods to match number of primitive methods in typeclass, and their signatures
data Instance : (tc : Typeclass n) -> Type where
  Inst : (MMTypeCtr n, List Method) -> Instance tc

numArgs : Monotype -> Nat
numArgs (Term _) = 0
numArgs (NullaryTypeAppl _) = 0
numArgs (FuncType (_, f)) = S (numArgs f)

mapType : (Monotype, Monotype)
mapType =
  ( FuncType (Term "a", Term "b")
  , FuncType (
      NullaryTypeAppl (TypeCtr "f", Term "a"),
      NullaryTypeAppl (TypeCtr "f", Term "b")
    )
  )

functorTC : Typeclass Z
functorTC = TyCl "Functor" [mapType]

functorInstances : List (Instance Main.functorTC)
functorInstances = map Inst [(Regular Z "Either", [Method' (mapType, MethodImpl' "Either.rmap")])]
