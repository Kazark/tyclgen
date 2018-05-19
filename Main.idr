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

data Method : (Monotype, Monotype) -> Type where
  Method' : (msig : (Monotype, Monotype)) -> String -> Method msig

||| Monomorphic type constructors
||| (S n) is the arity of the type constructor
data MMTypeCtr : (n : Nat) -> Type where
  Regular : (n: Nat) -> String -> MMTypeCtr n
  Tuple   : (n : Nat) -> MMTypeCtr n
  Array   : MMTypeCtr Z
  Appl1   : MMTypeCtr (S n) -> MMTypeCtr n

||| (S n) is the arity of the typeclass
||| The list is the methods that will be used to implement the others. You might
||| also call them abstract or pure virtual in object-oriented terminology.
data Typeclass : Nat -> List (Monotype, Monotype) -> Type where
  TyCl : String -> Typeclass n l

data Methods : List (Monotype, Monotype) -> Type where
  Nil  : Methods []
  (::) : Method msig -> Methods sigs -> Methods (msig :: sigs)

||| TODO Need number of methods to match number of primitive methods in typeclass, and their signatures
data Instance : (tc : Typeclass n l) -> Type where
  Inst : (MMTypeCtr n, Methods l) -> Instance tc

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

mapImpl : String -> Method Main.mapType
mapImpl = Method' mapType

functorTC : Typeclass Z [Main.mapType]
functorTC = TyCl "Functor"

functorInstances : List (Instance Main.functorTC)
functorInstances = map Inst
  [ (Appl1 (Regular 1 "Either"), [mapImpl "Either.rmap"])
  , (Appl1 (Regular 1 "Result"), [mapImpl "Result.mapError"])
  , (Regular Z "list", [mapImpl "List.map"])
  , (Regular Z "option", [mapImpl "Option.map"])
  , (Array, [mapImpl "Array.map"])
  , (Appl1 (Tuple 1), [mapImpl "Pair.map"])
  ]
