module BoundAst

%default total
%access public export

mutual
  ||| An unary type operator is a type of kind * -> *
  data UnaryTypeOp
    = TypeclassCtr
    --| TypeCtr String
    | NAryTypeAppl UnaryTypeOp Monotype

  ||| A monotype is a type of kind *
  data Monotype : Type where
    Term : String -> Monotype
    FuncType : Monotype -> Monotype -> Monotype
    TypeFullyApplied : UnaryTypeOp -> Monotype -> Monotype

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

