
-- Incomplete. It occurs to me that the set of variables occurring in a
-- ABT needs to be tracked.

record Valence S where
  constructor MkValence
  vaSort : S
  vaBinds : List S

record Arity S where
  constructor MkArity
  arSort : S
  arArgs : List (Valence S)

record Wrld where
  constructor MkWrld
  sorts : Type
  ops   : Arity sorts -> Type
  vars  : sorts -> Type

data VarList : (w : Wrld) -> List (sorts w) -> Type where
  Nil  : VarList w []
  (::) : {s : sorts w} -> (v : vars w s) -> VarList w ss -> VarList w (s::ss)

mutual
  data ABTList : (w : Wrld) -> List (Valence (sorts w)) -> Type where
    Nil  : ABTList w []
    (::) : ABT w s -> ABTList w ss -> ABTList w (s :: ss)

  data ABT : (w : Wrld) -> sorts w -> Type where
    V  : {w : Wrld} -> {s : sorts w} -> (v : vars w s) -> ABT w s
    Op : {w : Wrld} -> {a : Arity (sorts w)} -> (op : ops w a) -> ABTList w (arArgs a) -> ABT w (arSort a)


-- concrete example
data MySort = Exp | Stat
data MyOp : Arity MySort -> Type where
  Lit   : Int -> MyOp (MkArity Exp  [])
  Neg   :        MyOp (MkArity Exp  [MkValence Exp []])
  Print :        MyOp (MkArity Stat [MkValence Exp []])
  Plus  :        MyOp (MkArity Exp  [MkValence Exp [], MkValence Exp []])
  Sequ  :        MyOp (MkArity Stat [MkValence Stat [], MkValence Stat []])
  Sum   :        MyOp (MkArity Exp  [MkValence Exp [Exp]])
  Intgrl :       MyOp (MkArity Exp  [MkValence Exp [Exp, Exp]])
  Lam   :        MyOp (MkArity Exp  [MkValence Exp [Exp]])

data MyVar : MySort -> Type where
  MkMyVar : String -> MyVar Exp

wrld : Wrld
wrld = MkWrld MySort MyOp MyVar

{- 
ast : ABT Main.wrld Exp
ast = 
-}
