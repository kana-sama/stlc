{-# LANGUAGE OverloadedStrings, ViewPatterns #-}

module STLC.Dependent where

import Prelude.Unicode
import Data.String
import Control.Monad

infixl 5 :@
infixr 0 :⇒

type Name = String
type Context = [(Name, Term)]

data Term
  = U
  | Π (Name, Term) Term
  | Var Name
  | Name :⇒ Term
  | Term :@ Term
  deriving (Eq)

normal :: Term -> Term
normal U = U
normal (Π (x, α) β) = (Π (x, normal α) (normal β))
normal (Var x) = Var x
normal (x :⇒ t) = x :⇒ normal t
normal (Var "the" :@ α :@ τ) = normal τ
normal (t₁ :@ t₂) =
  case (normal t₁, normal t₂) of
    (x :⇒ t, t₂') -> substitute x t₂' t
    (t₁', t₂') -> t₁' :@ t₂'

substitute :: Name → Term → Term → Term
substitute x t₁ U = U
substitute x t₁ (Π (y, α) β) | x == y = Π (y, α) β
substitute x t₁ (Π (y, α) β) = Π (y, substitute x t₁ α) (substitute x t₁ β)
substitute x t₁ (Var y) | x == y = t₁
substitute x t₁ (Var y) = Var y
substitute x t₁ (y :⇒ t₂) | x == y = y :⇒ t₂
substitute x t₁ (y :⇒ t₂) = y :⇒ substitute x t₁ t₂
substitute x t₁ (t₂ :@ t₃) = normal (substitute x t₁ t₂ :@ substitute x t₁ t₃)

infer :: Context → Term → Maybe Term
infer г U = pure U
infer г (Var x) = lookup x г
infer г (t₁ :@ t₂) = do
  Π (x, α) β ← infer г t₁
  check г t₂ α
  pure (substitute x t₂ β)
infer _ _ = Nothing

check :: Context → Term → Term → Maybe ()
check г (x :⇒ t) γ@(Π (x', α) β) = do
  check г γ U
  check ((x, α) : г) t β
check г (Π (x, α) β) U = do
  check г α U
  check ((x, α) : г) β U
check г t τ = do
  τ' ← infer г t
  guard (τ ≡ τ')




defaultContext :: Context
defaultContext =
  [ ("N", U)
  , ("zero", "N")
  , ("succ", Π ("_", "N") "N")
  , ("elim-N",
    let zero = "zero"
        succ x = "succ" :@ x
        p x = "P" :@ x
        base = (p zero)
        step = (Π ("n", "N") (p "n" ~> p (succ "n")))
    in Π ("P", "N" ~> U) (base ~> step ~> Π ("n", "N") (p "n"))
  )
  , ("elim-N'",
    let zero = "zero"
        succ x = "succ" :@ x
        p x = "P" :@ x
        base = (p zero)
        step = (Π ("n", "N") (p "n" ~> p (succ "n")))
    in Π ("n", "N") (Π ("P", "N" ~> U) (base ~> step ~> p "n"))
  )
  , ("Id", Π ("α", U) ("α" ~> "α" ~> U))
  , ("refl", Π ("α", U) (Π ("x", "α") ("Id" :@ "α" :@ "x" :@ "x")))
  , ("the", Π ("α", U) (Π ("_", "α") "α"))
  ] where
    infixr 0 ~>
    α ~> β = Π ("_", α) β

main = do
  infer' "the"
  infer' n
  infer' $ "the" :@ n
  infer' $ "the" :@ (n ~> n)
  infer' $ the (n ~> n) "succ"
  infer' $ the (n ~> n) "succ" :@ zero
  infer' $ the (n ~> n) zero
  infer' $ "the" :@ n :@ "zero"
  infer' $ the (the (n ~> U) ("_" :⇒ n) :@ zero) zero
  infer' $ the n "succ"
  infer' $ the n (succ zero)
  infer' $ "elim-N'"
  infer' $ "elim-N'" :@ zero
  infer' $ "elim-N"
  infer' $ refl n (succ zero)
  infer' $ "elim-N" :@ ("n" :⇒ id n "n" zero) :@ (refl n zero)
  where
    infixr 0 ~>
    α ~> β = Π ("_", α) β
    n = "N"
    zero = "zero"
    succ x = "succ" :@ x
    the α t = "the" :@ α :@ t
    id α x y = "Id" :@ α :@ x :@ y
    refl α x = "refl" :@ α :@ x
    infer' t = do
      putStr "> :t "
      print t
      case infer defaultContext (normal t) of
        Just τ -> print τ
        Nothing -> putStrLn "error"
        
instance IsString Term where
  fromString = Var


isNat :: Term → Maybe Int
isNat (Var "zero") = Just 0
isNat (Var "succ" :@ next) = fmap (+ 1) (isNat next)
isNat _ = Nothing

instance Show Term where
  show (isNat → Just n) = show n
  show U = "U"
  show (Π ("_", α@(Π _ _)) β) = "(" ++ show α ++ ")" ++ " → " ++ show β
  show (Π ("_", α) β) = show α ++ " → " ++ show β
  show (Π (x, α) β) = "(" ++ x ++ " : " ++ show α ++ ") → " ++ show β
  show (Var x) = x
  show (x :⇒ t) = "λ" ++ x ++ ". " ++ show t
  show (t₁ :@ t₂) = parens parens₁ "" (show t₁) " " ++ parens parens₂ "" (show t₂) ""
    where
      parens₁ = case t₁ of { _ :⇒ _ -> True; _ -> False }
      parens₂ = case t₂ of { Var _ -> False; U -> False; _ -> True }
      parens True _ x _ = "(" ++ x ++ ")"
      parens False b x a = b ++ x ++ a