module STLC.Bi2 where

import Control.Monad.Except

data Kind = Star
data Name = Const String | Bound Int | Unquoted Int deriving (Eq)
data Type = TPar Name | Type :->: Type deriving (Eq)
data TermI = The Type TermC | Var Int | Par Name | TermI :@: TermC
data TermC = Inf TermI | Lam TermC
data Binding = HasType Type | HasKind Kind
type Context = [(Name, Binding)]

-- data Neutral = NPar Name | NApp Neutral Value
-- data Value = VLam (Value -> Value) | VNeutral Neutral
-- type Env = [Value]

-- evalI :: TermI -> Env -> Value
-- evalI (The _ e) d = evalC e d
-- evalI (Var i) d = d !! i
-- evalI (Par x) d = VNeutral (NPar x)
-- evalI (e1 :@: e2) d =
--   case evalI e1 d of
--     VLam f -> f (evalI e2 d)
--     VNeutral n ->  VNeutral (NApp n (evalI e2 d)) 

-- evalC :: TermI -> Env -> Value
-- evalC (Inf e) d = evalI e d
-- evalC (Lam e) d = VLam (\x -> evalC e (x : d))

type TC a = Except String a

checkKind :: Context -> Type -> Kind -> TC ()
checkKind ctx (TPar x) Star =
  case lookup x ctx of
    Just (HasKind Star) -> pure ()
    Nothing -> throwError "unknown type identifier"
checkKind ctx (α :->: β) Star = do
  checkKind ctx α Star
  checkKind ctx β Star

inferType0 :: Context -> TermI -> TC Type
inferType0 = inferType 0

inferType :: Int -> Context -> TermI -> TC Type
inferType i ctx (The τ e) = do
  checkKind ctx τ Star
  checkType i ctx e τ
  pure τ
inferType i ctx (Par x) =
  case lookup x ctx of
    Just (HasType τ) -> pure τ
    Nothing -> throwError "unknown term identifier"
inferType i ctx (e1 :@: e2) = do
  inferType i ctx e1 >>= \case
    α :->: β -> do
      checkType i ctx e2 α
      pure β
    _ -> throwError "illegal application"

checkType :: Int -> Context -> TermC -> Type -> TC ()
checkType i ctx (Inf e) τ = do
  τ' <- inferType i ctx e
  unless (τ == τ') (throwError "type mismatch")
checkType i ctx (Lam e) (α :->: β) =
  checkType (i + 1) ((Bound i, HasType α) : ctx) (substC 0 (Par (Bound i)) e) β
checkType _ _ _ _ = throwError "type mismatch"

substC :: Int -> TermI -> TermC -> TermC
substC = undefined