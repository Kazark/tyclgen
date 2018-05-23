module Instances

import BoundAst

%default total

MapType : (Monotype, Monotype)
MapType =
  ( FuncType (Term "a") (Term "b")
  , FuncType
    (NullaryTypeAppl TypeclassCtr (Term "a"))
    (NullaryTypeAppl TypeclassCtr (Term "b"))
  )

mapImpl : String -> Method MapType
mapImpl = Method' _

FunctorTC : Typeclass Z [MapType]
FunctorTC = TyCl "Functor"

functorInstances : List (Instance FunctorTC)
functorInstances = map Inst
  [ (Appl1 (Regular 1 "Either"), [mapImpl "Either.rmap"])
  , (Appl1 (Regular 1 "Result"), [mapImpl "Result.mapError"])
  , (Regular Z "list", [mapImpl "List.map"])
  , (Regular Z "option", [mapImpl "Option.map"])
  , (Array, [mapImpl "Array.map"])
  , (Appl1 (Tuple 1), [mapImpl "Pair.map"])
  ]

BindType : (Monotype, Monotype)
BindType =
  ( FuncType (Term "a") (NullaryTypeAppl TypeclassCtr (Term "b"))
  , FuncType
    (NullaryTypeAppl TypeclassCtr (Term "a"))
    (NullaryTypeAppl TypeclassCtr (Term "b"))
  )

ApplyType : (Monotype, Monotype)
ApplyType =
  ( NullaryTypeAppl TypeclassCtr (FuncType (Term "a") (Term "b"))
  , FuncType
    (NullaryTypeAppl TypeclassCtr (Term "a"))
    (NullaryTypeAppl TypeclassCtr (Term "b"))
  )

--TraverseType : (Monotype, Monotype)
--TraverseType =
--  ( FuncType (Term "a") (NullaryTypeAppl (TypeCtr "m") (Term "b"))
--  , FuncType
--    (NullaryTypeAppl TypeclassCtr (Term "a"))
--    (NullaryTypeAppl (TypeCtr "m") (NullaryTypeAppl TypeclassCtr (Term "b")))
--  )

BimapType : (Monotype, Monotype)
BimapType =
  ( FuncType (Term "a") (Term "b")
  , FuncType
    (FuncType (Term "c") (Term "d"))
    (FuncType
      (NullaryTypeAppl (NAryTypeAppl TypeclassCtr (Term "a")) (Term "c"))
      (NullaryTypeAppl (NAryTypeAppl TypeclassCtr (Term "b")) (Term "d"))
    )
  )

TrimapType : (Monotype, Monotype)
TrimapType =
  ( FuncType (Term "a") (Term "b")
  , FuncType
    (FuncType (Term "c") (Term "d"))
    (FuncType
        (FuncType (Term "e") (Term "f"))
        (FuncType
            (NullaryTypeAppl (NAryTypeAppl (NAryTypeAppl TypeclassCtr (Term "a")) (Term "c")) (Term "e"))
            (NullaryTypeAppl (NAryTypeAppl (NAryTypeAppl TypeclassCtr (Term "b")) (Term "d")) (Term "f"))
        )
    )
  )
