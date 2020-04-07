module STLC.Traditional where

import Control.Monad

type Name = String

data Type
  = Bool
  | Type :→ Type
  deriving (Eq, Show)

data Term
  = Var Name
  | Lam (Name, Type) Term
  | Term :@ Term
  | TT
  | FF
  | If Term Term Term

type Context = [(Name, Type)]

infer :: Context -> Term -> Maybe Type
infer г (Var x) = lookup x г
infer г (Lam (x, α) t) = do
  β <- infer ((x, α) : г) t
  pure (α :→ β)
infer г (t₁ :@ t₂) = do
  α₁ :→ β <- infer г t₁
  α₂ <- infer г t₂
  guard (α₁ == α₂)
  pure β
infer _ TT = pure Bool
infer _ FF = pure Bool
infer г (If t₁ t₂ t₃) = do
  Bool <- infer г t₁
  α₁ <- infer г t₂
  α₂ <- infer г t₃
  guard (α₁ == α₂)
  pure α₁

main :: IO ()
main = do
  print $ infer [] (Var "x")
  print $ infer [("x", Bool)] (Var "x")
  print $ infer [] (Lam ("x", Bool) (Var "x"))
  print $ infer [("y", Bool)] ((Lam ("x", Bool) (Var "x")) :@ (Var "y"))
