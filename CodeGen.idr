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
