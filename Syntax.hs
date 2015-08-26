module Syntax(Term(..),
              app, lam, var, n, d, p,
              dis, neg, con, imp, iff, forall, exists,
              typeOf,
              freeVars,
              Type,
              leftType, rightType) where

import Data.List as L

data Term
  = App Term Term
  | Lam TVar Term
  | Var TVar
  | Neg
  | Dis
  | Pi Type
    deriving (Eq, Ord)

-- Basic constructors
app l r =
  case isFuncType (typeOf l) && leftType (typeOf l) == typeOf r of
   True -> App l r
   False -> error $ "app: Illegal arguments " ++ show l ++ ", " ++ show r
lam v t = Lam v t
var v = Var v
n = Neg
d = Dis
p t = Pi t

-- Derived constructors for logical rules
dis a b = app (app d a) b
neg a = app n a
con a b = neg (dis (neg a) (neg b))
imp a b = dis (neg a) b
iff a b = con (imp a b) (imp b a)
forall v a = app (p $ varType v) (lam v a)
exists v a = neg $ forall v (neg a)
eqp t =
  let a = tVar "a" t
      b = tVar "b" t
      f = tVar "f" (func t o) in
   lam a $ lam b $ forall f $ imp (app (var f) (var a)) (app (var f) (var b))

typeOf (App l r) = rightType (typeOf l)
typeOf (Lam v t) = func (varType v) (typeOf t)
typeOf (Var v) = varType v
typeOf Dis = func o (func o o)
typeOf Neg = func o o
typeOf (Pi t) = func (func t o) o

freeVars :: Term -> [TVar]
freeVars (Var v) = [v]
freeVars (App l r) = freeVars l ++ freeVars r
freeVars (Lam v t) = L.filter (\a -> a /= v) $ freeVars t
freeVars Neg = []
freeVars Dis = []
freeVars (Pi _) = []

data TVar = TVar String Type
          deriving (Eq, Ord)

tVar n t = TVar n t

varType (TVar _ t) = t

data Type
  = O
  | I
  | Func Type Type
    deriving (Eq, Ord)

o = O
i = I
func l r = Func l r

isFuncType (Func _ _) = True
isFuncType _ = False

rightType (Func _ r) = r

leftType (Func l _) = l

instance Show Term where
  show (App l r) = "[" ++ show l ++ " " ++ show r ++ "]"
  show (Lam v t) = "[\\" ++ show v ++ ". " ++ show t ++ "]"
  show (Var v) = show v
  show Neg = "~"
  show Dis = "\\/"
  show (Pi t) = "@"

instance Show Type where
  show O = "o"
  show I = "i"
  show (Func l r) = "(" ++ show r ++ show l ++ ")"

instance Show TVar where
  show (TVar n I) = n ++ "(" ++ show I ++ ")"
  show (TVar n O) = n ++ "(" ++ show O ++ ")"
  show (TVar n t) = n ++ show t
