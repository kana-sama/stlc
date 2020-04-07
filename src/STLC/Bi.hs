module STLC.Bi where

import Prelude.Unicode
import Control.Monad

type Name = String

data Type
  = 𝔹
  | Type :→ Type
  deriving (Eq)

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
infer г (The τ t) = do
  check г t τ
  pure τ
infer г (t₁ :@ t₂) = do
  α :→ β ← infer г t₁
  check г t₂ α
  pure β
infer _ _ = Nothing

check :: Context → Term → Type → Maybe ()
check г (x :⇒ t) (α :→ β) = check ((x, α) : г) t β
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


--------------------------------

infixr 0 :→, :⇒

instance Show Type where
  show 𝔹 = "𝔹"
  show (α@(_ :→ _) :→ β) = "(" ++ show α ++ ") → " ++ show β
  show (α :→ β) = show α ++ " → " ++ show β

instance Show Term where
  show (Var x) = x
  show (x :⇒ t) = "λ" ++ x ++ showBody t where
    showBody (x' :⇒ t') = " " ++ x' ++ showBody t'
    showBody t = ". " ++ show t
  show (t₁ :@ t₂)   = t₁' ++ t₂' where
    t₁' = case t₁ of
      _ :⇒ _ -> "(" ++ show t₁ ++ ")"
      _ -> show t₁
    t₂' = case t₂ of  
      Var _ -> " " ++ show t₂
      TT -> " " ++ show t₂
      FF -> " " ++ show t₂
      _ -> "(" ++ show t₂ ++ ")"
  show TT = "true"
  show FF = "false"
  show (If t₁ t₂ t₃) = "if " ++ show t₁ ++ " then " ++ show t₂ ++ " else " ++ show t₃
  show (Let x t₁ t₂) = "let " ++ x ++ " = " ++ show t₁ ++ " in " ++ show t₂
  show (The τ t) = "(" ++ t' ++ " : " ++ show τ ++ ")" where
    t' = case t of
      Var _ -> show t
      TT -> show t
      FF -> show t
      _ -> "(" ++ show t ++ ")"

main :: IO ()
main = do
  let not = "x" :⇒ If (Var "x") FF TT
  check' [] not (𝔹 :→ 𝔹)
  check' [("¬", (𝔹 :→ 𝔹)), ("x", 𝔹)] (Var "¬" :@ Var "x") 𝔹
  check' [("¬", (𝔹 :→ 𝔹)), ("x", 𝔹)] ((The (𝔹 :→ 𝔹) not) :@ Var "x") 𝔹
  check' [] (The (𝔹 :→ 𝔹) ("x" :⇒ Let "z" (Var "x") (Var "z"))) (𝔹 :→ 𝔹)
  check' [] (The (𝔹 :→ 𝔹) ("x" :⇒ The 𝔹 (Var "x"))) (𝔹 :→ 𝔹)
  check' [] ((The (𝔹 :→ 𝔹) ("x" :⇒ The 𝔹 (Var "x"))) :@ TT) 𝔹
  check' [] ("x" :⇒ (Var "x")) (𝔹 :→ 𝔹)
  check' [] ("f" :⇒ "g" :⇒ "x" :⇒ Var "f" :@ (Var "g" :@ Var "x")) ((𝔹 :→ 𝔹) :→ (𝔹 :→ 𝔹) :→ (𝔹 :→ 𝔹))
    where
      check' ctx term ty = do
        putStr "> :t "
        print term
        case check ctx term ty of
          Just _ -> print ty
          Nothing -> putStrLn "error"
        