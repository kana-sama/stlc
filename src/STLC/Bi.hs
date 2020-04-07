module STLC.Bi where

import Prelude.Unicode
import Control.Monad

type Name = String

data Type
  = 𝔹
  | Type :→ Type
  deriving (Eq, Show)

data Term
  = Var Name
  | Name :⇒ Term
  | Term :@ Term
  | TT
  | FF
  | If Term Term Term
  | The Type Term
  | Let Name Term Term

type Context = [(Name, Type)]

infer :: Context → Term → Maybe Type
infer г TT = pure 𝔹
infer г FF = pure 𝔹
infer г (Var x) = lookup x г
infer г (The τ t) = check г t τ
infer г (t₁ :@ t₂) = do
  α :→ β ← infer г t₁
  check г t₂ α
  pure β
infer _ _ = Nothing

check :: Context → Term → Type → Maybe Type
check г (x :⇒ t) (α :→ β) = do
  check ((x, α) : г) t β
  pure (α :→ β)
check г (If t₁ t₂ t₃) τ = do
  check г t₁ 𝔹
  check г t₂ τ
  check г t₃ τ
check г (Let x t₁ t₂) τ = do
  α ← infer г t₁
  check ((x, α) : г) t₂ τ
check г t τ = do
  τ' ← infer г t
  guard (τ ≡ τ')
  pure τ

main :: IO ()
main = do
  let not = "x" :⇒ If (Var "x") FF TT
  print $ check [] not (𝔹 :→ 𝔹)
  print $ check [("¬", (𝔹 :→ 𝔹)), ("x", 𝔹)] (Var "¬" :@ Var "x") 𝔹
  print $ check [("¬", (𝔹 :→ 𝔹)), ("x", 𝔹)] ((The (𝔹 :→ 𝔹) not) :@ Var "x") 𝔹
  print $ check [] (The (𝔹 :→ 𝔹) ("x" :⇒ Let "z" (Var "x") (Var "z"))) (𝔹 :→ 𝔹)
  print $ check [] (The (𝔹 :→ 𝔹) ("x" :⇒ The 𝔹 (Var "x"))) (𝔹 :→ 𝔹)
  print $ check [] ("x" :⇒ (Var "x")) (𝔹 :→ 𝔹)