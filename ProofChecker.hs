module ProofChecker(
  thmTerm,
  in_mp,
  ax_disp, ax_impp, ax_rm_dis) where

import Data.List as L

import Syntax
import Type

data Theorem
  = Theorem Term
    deriving (Eq, Ord, Show)
             
thm t = Theorem t
thmTerm (Theorem t) = t

-- Axioms
ax_disp p = thm $ imp (dis p p) p
ax_impp p = thm $ imp p (dis p p)
ax_dis_comm p q = thm $ imp (dis p q) (dis q p)
ax_rm_dis p q r = thm $ imp p (imp q (imp (dis r p) (dis r q)))
ax_inst f x = thm $ imp (app (p (leftType $ typeOf f)) f) (app f x)
ax_forall_dist pred f x = thm $
  imp
  (forall x (dis pred (app f (var x))))
  (dis pred (app (p (leftType $ typeOf f)) f))

-- Inference rules
in_rename tp y =
   case isLam $ thmTerm tp of
    True ->
      let t = thmTerm tp
          v = getLamVar t
          lt = getLamTerm t in
       case (not $ occursIn y lt) && (not $ boundIn v lt) of
        True -> thm $ Lam y $ renameVar v y lt
        False -> error $ "in_rename: bad arguments " ++ show tp ++ " " ++ show y
    False -> error $ "in_rename: bad argument " ++ show tp

in_contract tp =
  thm $ contract $ thmTerm tp

in_expand c td a =
  case contract (app (thmTerm td) a) == c of
   True -> thm c
   False ->
     error $ "in_expand: bad arguments " ++ show c ++ " " ++ show td ++ " " ++ show a

in_mp tp tq =
  let p = thmTerm tp
      q = thmTerm tq in
   case p of
    (App (App Dis (App Neg a)) b) ->
      case a == q of
       True -> thm b
       False -> error $ "in_mp: bad arguments " ++ show p ++ " " ++ show q
    _ -> error $ "in_mp: bad arguments " ++ show p ++ " " ++ show q

in_gen fxt =
  let fx = thmTerm fxt in
  case fx of
   (App f (Var x)) ->
     case L.elem x $ freeVars f of
      True -> error $ "in_gen: bad argument " ++ show fxt
      False -> thm $ app (p $ leftType $ typeOf f) f
   _ -> error $ "in_gen: bad argument " ++ show fxt

in_sub fxt a =
  let fx = thmTerm fxt in
  case fx of
   (App f (Var x)) ->
     case L.elem x $ freeVars f of
      True -> error $ "in_gen: bad argument " ++ show fxt
      False -> thm $ app f a
   _ -> error $ "in_gen: bad argument " ++ show fxt
