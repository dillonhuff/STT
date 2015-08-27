module Syntax(Term(..),
              app, lam, var, n, d, p,
              dis, neg, con, imp, iff, forall, exists,
              typeOf,
              isLam,
              getLamVar, getLamTerm,
              freeVars, occursIn, boundIn,
              contract, renameVar,
              TVar,
              tVar) where

import Data.Set as S

import Type

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

isLam (Lam _ _) = True
isLam _ = False

getLamVar (Lam v _) = v
getLamTerm (Lam _ t) = t

occursIn v t = S.member v $ S.union (boundVars t) (freeVars t)

freeVars :: Term -> Set TVar
freeVars (Var v) = S.singleton v
freeVars (App l r) = S.union (freeVars l) (freeVars r)
freeVars (Lam v t) = S.filter (\a -> a /= v) $ freeVars t
freeVars Neg = S.empty
freeVars Dis = S.empty
freeVars (Pi _) = S.empty

boundIn v t = S.member v $ boundVars t

boundVars :: Term -> Set TVar
boundVars (Lam v t) = S.union (S.singleton v) $ boundVars t
boundVars _ = S.empty

-- Lambda conversion functions
renameVar t r (App a b) = App (renameVar t r a) (renameVar t r b)
renameVar t r (Lam v b) =
  case v == t of
   True -> Lam r (renameVar t r b)
   False -> Lam v (renameVar t r b)
renameVar t r (Var x) =
  case x == t of
   True -> Var r
   False -> Var x
renameVar _ _ t = t

subsTerm target result t =
  case t == target of
   True -> result
   False ->
     case t of
      (App a b) -> App (subsTerm target result a) (subsTerm target result b)
      (Lam v t) -> Lam v $ subsTerm target result t
      _ -> t

contract t@(App (Lam x b) a) =
  case (not $ boundIn x b) &&
       (S.intersection (boundVars b) (freeVars a) == S.empty) of
   True -> subsTerm (Var x) a b
   False -> error $ "contract: bad argument " ++ show t
contract t = error $ "contract: bad argument " ++ show t

data TVar = TVar String Type
          deriving (Eq, Ord)

tVar n t = TVar n t

varType (TVar _ t) = t

instance Show Term where
  show (App l r) = "[" ++ show l ++ " " ++ show r ++ "]"
  show (Lam v t) = "[\\" ++ show v ++ ". " ++ show t ++ "]"
  show (Var v) = show v
  show Neg = "~"
  show Dis = "\\/"
  show (Pi t) = "@"

instance Show TVar where
  show (TVar n t) = n ++ show t
