module Type(Type,
            o, i, func,
            isFuncType,
            leftType, rightType) where

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

instance Show Type where
  show O = "o"
  show I = "i"
  show (Func l r) = "(" ++ show r ++ show l ++ ")"
