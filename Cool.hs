module Cool where

-- Code from the first half of the paper
-- I am not a number - I am a free variable
--   by Connor McBride and James McKinna
-- https://pdfs.semanticscholar.org/1df1/a0b5e9d14855e24deb7cd602bdef9445a435.pdf

infixl 6 :$

type Name = String
data Expr = F Name         -- free variables
          | B Int          -- bound variables
          | Expr :$ Expr   -- application
          | Expr :-> Scope -- forall _ . _
  deriving (Show,Eq)
  -- Expr are understood to be "closed" (no bound variables pointing out of scope)
  
newtype Scope = Sc Expr deriving (Show,Eq)
  -- Sc'd Exprs are understood to have one dangling bound variable B 0

-- Convert an Expr into a Scope by replacing a free variable `name' with B i
-- i is the number of binders down from the top... the "de Bruijn" index
abstract :: Name -> Expr -> Scope
abstract name expr = Sc (nameTo 0 expr) where
  nameTo outer e = case e of
    F name' | name == name' -> B outer
            | otherwise     -> F name'
    B ix                    -> B ix
    fun :$ arg              -> nameTo outer fun :$ nameTo outer arg
    dom :-> Sc body         -> nameTo outer dom :-> Sc (nameTo (outer+1) body)

-- Fill in the dangling variable of Scope with an Expr
instantiate :: Expr -> Scope -> Expr
instantiate image (Sc body) = replace 0 body where
  replace outer e = case e of
    B index | index == outer -> image
            | otherwise      -> B index
    F name                   -> F name
    fun :$ arg               -> replace outer fun :$ replace outer arg
    dom :-> Sc body          -> replace outer dom :-> Sc (replace (outer+1) body)

-- From now on B and Sc are off limits. There are no more de Bruijn numbers
-- only free variables and the abstract / instantiate operations.

-- Implement substitution safely using abstract and instantiate. Ha!
substitute :: Expr -> Name -> Expr -> Expr
substitute image name = instantiate image . abstract name

-- attempt to split up an application
unapply :: Expr -> Maybe (Expr, Expr)
unapply (fun :$ arg) = Just (fun, arg)
unapply _            = Nothing

data Binding = Name :∈ Expr
  deriving (Show,Eq)

bName :: Binding -> Name
bName (name :∈ _) = name

bVar :: Binding -> Expr
bVar = F . bName

infixr 4 --->

-- wrap an expr in a quantifier
(--->) :: Binding -> Expr -> Expr
(name :∈ dom) ---> range = dom :-> abstract name range

-- pick a name for the quantified variable and split whole expr into binding and body with name substituted
(<---) :: Name -> Expr -> Maybe (Binding, Expr)
name <--- (dom :-> scope) = Just (name :∈ dom, instantiate (F name) scope)
name <--- _               = Nothing

ex1 :: Expr -- forall x in the Bar, x is drinking
ex1 = F "Bar" :-> Sc (F "IsDrinking" :$ B 0)

ex2 :: Expr -- forall x y ∈ N, x = y OR x /= y
ex2 = ("x" :∈ F "N") ---> ("y" :∈ F "N") ---> F "OR" :$ (F "=" :$ F "x" :$ F "y") :$ (F "/=" :$ F "x" :$ F "y")

pretty :: Expr -> String
pretty e = case e of
  F name          -> name
  B index         -> show index
  fun :$ arg      -> "(" ++ pretty fun ++ " " ++ pretty arg ++ ")"
  dom :-> Sc body -> "(∀_∈" ++ pretty dom ++ " . " ++ pretty body ++ ")"

newtype Pretty = Pretty { ugly :: Expr }

instance Show Pretty where
  show = pretty . ugly


