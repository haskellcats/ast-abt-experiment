
record Arity S where
  constructor MkArity
  arSort : S
  arArgs : List S

record Wrld where
  constructor MkWrld
  sorts : Type
  ops   : Arity sorts -> Type
  vars  : sorts -> Type

mutual
  data ASTList : (w : Wrld) -> List (sorts w) -> Type where
    Nil : ASTList w []
    (::) : AST w s -> ASTList w ss -> ASTList w (s :: ss)

  data AST : (w : Wrld) -> sorts w -> Type where
    V  : {w : Wrld} -> {s : sorts w} -> (v : vars w s) -> AST w s
    Op : {w : Wrld} -> {a : Arity (sorts w)} -> (op : ops w a) -> ASTList w (arArgs a) -> AST w (arSort a)


{-
structuralInduction :
  (w : Wrld) ->
  (s : sorts w) ->
  (P : AST w s -> Type) ->
  ((s : sorts w) -> (v : vars w s) -> P (V v)) ->
  ((a : Arity (sorts w)) -> (op : ops w a) -> P (Op op ...... urg
      (forany arity, any op, every position of arity a, every ast with
         sort of a, then you have P (Op op asts))
  (ast : AST w s -> P ast)

abstract syntax trees come with an induction principle which allows
construction of (unique) (dependent) functions on ASTs by providing functions
that operate on variables and the subtrees within operators.
-}

-- substitute replacement for every occurrence of subj in target
{- I don't have decEq for variables... if variables were themselves types though...
   this algorithm is an application of structural induction
substitution : (subj : vars w s') -> (replacement : AST w s') -> (target : AST w s) -> AST w s
substitution x b (V x) = b
substitution x b (V y) = V y
substitution x b (Op args) = map (Op . substitition x b) args
-}

-- Theorem 1.1. (substitution is a well-defined operation)
-- If a ∈ A[X, x], then for every b ∈ A[X]
-- there exists a unique c ∈ A[X] such that [b/x]a = c
--
-- That's the form of a universal property

-- concrete example
data MySort = Exp | Stat
data MyOp : Arity MySort -> Type where
  Lit : Int -> MyOp (MkArity Exp [])    -- numeric literal, no args
  Plus : MyOp (MkArity Exp [Exp,Exp])   -- add two expressions
  Neg : MyOp (MkArity Exp [Exp])        -- negate an expression
  Print : MyOp (MkArity Stat [Exp])     -- print an expression
  Sequ : MyOp (MkArity Stat [Stat,Stat]) -- do one statement after the other

data MyVar : MySort -> Type where
  EVar : String -> MyVar Exp
  SVar : String -> MyVar Stat

wrld : Wrld
wrld = MkWrld MySort MyOp MyVar

{- doesn't compile because [ ] syntax can't disambiguate
ast : AST Main.wrld Exp
ast = Op Sequ
  [ Op Print [Op Plus [Op (Lit 9) [], V (EVar "x")]]
  , Op Print [Op (Lit 9) []]
  ]
-}
