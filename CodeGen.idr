module CodeGen

%default total

||| Stands for "Static Method Inline"
record SMI where
  constructor StMeIn
  name : String
  args : List String
  retT : String
  impl : String

genSMI : SMI -> String
genSMI x =
  let argz = concat $ intersperse "," $ args x
  in concat ["  static member inline ", name x, " (", argz, ") : ", retT x, " = ", impl x]

data AutoOpen = AutoOpen'

record NSAndModule where
  constructor NSNModule
  maybeModule : Maybe (String, Maybe AutoOpen)
  ns : String

nsOnly : String -> NSAndModule
nsOnly ns = NSNModule Nothing ns

record FSFile where
  constructor FSF
  nsm : NSAndModule
  type : (String, List (List SMI))

maybeGenAutoOpen : Maybe AutoOpen -> List String -> List String
maybeGenAutoOpen Nothing = id
maybeGenAutoOpen (Just AutoOpen') = (::) "[<AutoOpen>]"

genNSAndModule : NSAndModule -> List String
genNSAndModule nsam =
  case maybeModule nsam of
    Nothing => [ "namespace " ++ ns nsam, ""]
    Just (modName, maybeAutoOpen) => maybeGenAutoOpen maybeAutoOpen
      [ "module " ++ ns nsam ++ "." ++ modName
      , ""
      ]

genClass : String -> List String
genClass x = ["type " ++ x ++ " () ="]

genHeader : FSFile -> List String
genHeader fsfile = genNSAndModule (nsm fsfile) ++ genClass (fst $ type fsfile)

genClassBody : List (List (SMI)) -> List String
genClassBody xs = xs >>= ((::) "" . map genSMI)

genFSFile : FSFile -> List String
genFSFile x = genHeader x ++ genClassBody (snd $ type x)
