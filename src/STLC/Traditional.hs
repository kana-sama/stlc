module STLC.Traditional where

import Prelude.Unicode
import Control.Monad

type Name = String

data Type
  = 𝔹
  | Type :→ Type
  deriving (Eq, Show)

data Term
  = Var Name
  | (Name, Type) :⇒ Term
  | Term :@ Term
  | TT
  | FF
  | If Term Term Term

type Context = [(Name, Type)]

infer :: Context → Term → Maybe Type
infer г (Var x) = lookup x г
infer г ((x, α) :⇒ t) = do
  β ← infer ((x, α) : г) t
  pure (α :→ β)
infer г (t₁ :@ t₂) = do
  α₁ :→ β ← infer г t₁
  α₂ ← infer г t₂
  guard (α₁ ≡ α₂)
  pure β
infer _ TT = pure 𝔹
infer _ FF = pure 𝔹
infer г (If t₁ t₂ t₃) = do
  𝔹 ← infer г t₁
  α₁ ← infer г t₂
  α₂ ← infer г t₃
  guard (α₁ ≡ α₂)
  pure α₁

main :: IO ()
main = do
  print $ infer [] (Var "x")
  print $ infer [("x", 𝔹)] (Var "x")
  print $ infer [] (("x", 𝔹) :⇒ Var "x")
  print $ infer [("y", 𝔹)] ((("x", 𝔹) :⇒ Var "x") :@ (Var "y"))
