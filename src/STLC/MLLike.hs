module STLC.MLLike where

import Control.Monad.Except
import Control.Monad.State
import Data.Traversable
import Data.Foldable

data Module
  = Module [Declaration]
  deriving (Show)

data Declaration
  = Declaration Name Expression
  deriving (Show)

data Expression
  = Lambda { args :: [(Name, Type)], body :: Expression }
  | Application Expression [Expression]
  | Variable Name
  | Let { name :: Name, value :: Expression, next :: Expression }
  | If { cond :: Expression, onTrue :: Expression, onFalse :: Expression }
  | Literal Literal
  deriving (Show)

data Literal
  = LInteger Integer
  | LString String
  | LBool Bool
  | LUnit
  deriving (Show)

data Type
  = Integer
  | String
  | Bool
  | Unit
  | Function { input :: [Type], output :: Type }
  deriving (Show, Eq)

newtype Name
  = Name String
  deriving (Show, Eq)

newtype TypeCheck a = TypeCheck (ExceptT TypeCheckError (State Context) a)
  deriving (Functor, Applicative, Monad)

data Binding = Binding Name Type
  deriving (Show)

newtype Context = Context { getScopes :: [[Binding]] }
  deriving (Show)

data TypeCheckError
  = NoSuchVariable Name
  | NotAFunction Expression
  | InvalidArguments { function :: Expression, expected :: [Type], actual :: [Type] }
  | InvalidConditionType Type
  | InvalidBranchesTypes Type Type
  deriving (Show)

getContext :: TypeCheck Context
getContext = TypeCheck get

bind :: Name -> Type -> TypeCheck ()
bind name ty = TypeCheck $ modify \context ->
  case context of
    Context [] ->
      Context [[binding]]
    Context (scope : scopes) ->
      Context ((binding : scope) : scopes)
  where
    binding = Binding name ty

withLocalScope :: TypeCheck a -> TypeCheck a
withLocalScope tc = do
  context <- getContext
  TypeCheck $ put (Context ([] : getScopes context))
  result <- tc
  TypeCheck $ put context
  pure result

typeCheckError :: TypeCheckError -> TypeCheck a
typeCheckError error = TypeCheck $ throwError error

assert :: Bool -> TypeCheckError -> TypeCheck ()
assert True _ = pure ()
assert False error = typeCheckError error

runTypeCheck :: TypeCheck a -> Context -> (Either TypeCheckError a, Context)
runTypeCheck (TypeCheck tc) context =
  runState (runExceptT tc) context

inferLiteralType :: Literal -> TypeCheck Type
inferLiteralType (LInteger _) = pure Integer
inferLiteralType (LString _) = pure String
inferLiteralType (LBool _) = pure Bool
inferLiteralType LUnit = pure Unit

inferExpressionType :: Expression -> TypeCheck Type
inferExpressionType (Literal lit) = inferLiteralType lit
inferExpressionType (Lambda args body) = withLocalScope do
  for args \(name, ty) ->
    bind name ty
  bodyTy <- inferExpressionType body
  pure $ Function (map snd args) bodyTy
inferExpressionType (Application func args) = do
  funcTy <- inferExpressionType func
  argsTy <- for args inferExpressionType
  assert (isFunctionType funcTy) $ NotAFunction func
  assert (input funcTy == argsTy) $
    InvalidArguments { function = func, expected = input funcTy, actual = argsTy }
  pure $ output funcTy
  where
    isFunctionType (Function _ _) = True
    isFunctionType _ = False
inferExpressionType (Variable name) = do
  Context context <- getContext
  case choiceMap (find \(Binding name' ty) -> name == name') context of
    Just (Binding _ ty) -> pure ty
    Nothing -> typeCheckError $ NoSuchVariable name
  where
    choiceMap f = asum . map f
inferExpressionType (Let name value next) = do
  valueTy <- inferExpressionType value
  withLocalScope do
    bind name valueTy
    inferExpressionType next
inferExpressionType (If cond onTrue onFalse) = do
  condTy <- inferExpressionType cond
  assert (condTy == Bool) $ InvalidConditionType condTy
  onTrueTy <- inferExpressionType onTrue
  onFalseTy <- inferExpressionType onFalse
  assert (onTrueTy == onFalseTy) $ InvalidBranchesTypes onTrueTy onFalseTy
  pure onTrueTy 

checkModule :: Module -> TypeCheck [(Name, Type)]
checkModule (Module declarations) = do
  for declarations \(Declaration name value) -> do
    valueTy <- withLocalScope $ inferExpressionType value
    bind name valueTy
    pure (name, valueTy)

example :: Module
example =
  Module
    [ Declaration (Name "f") $
        Lambda [(Name "a", Integer), (Name "b", Integer)] $
          Let (Name "c") (Application (Variable (Name "plus")) [Variable (Name "a"), Variable (Name "b")]) $
          Let (Name "a_s") (Application (Variable (Name "to_string")) [Variable (Name "a")]) $
          Let (Name "b_s") (Application (Variable (Name "to_string")) [Variable (Name "b")]) $
          Let (Name "c_s") (Application (Variable (Name "to_string")) [Variable (Name "c")]) $
          Let (Name "o") (Literal (LString "=> ")) $
          Let (Name "o") (Application (Variable (Name "str_concat")) [Variable (Name "o"), Variable (Name "a_s")]) $
          Let (Name "o") (Application (Variable (Name "str_concat")) [Variable (Name "o"), Literal (LString " + ")]) $
          Let (Name "o") (Application (Variable (Name "str_concat")) [Variable (Name "o"), Variable (Name "b_s")]) $
          Let (Name "o") (Application (Variable (Name "str_concat")) [Variable (Name "o"), Literal (LString " = ")]) $
          Let (Name "o") (Application (Variable (Name "str_concat")) [Variable (Name "o"), Variable (Name "c_s")]) $
          Let (Name "_") (Application (Variable (Name "print")) [Variable (Name "o")]) $
          Variable (Name "o")
    ]

defaultContext :: Context
defaultContext = Context [moduleScope, builtinScope]
  where
    moduleScope = []
    builtinScope =
      [ Binding (Name "eq") (Function [Integer, Integer] Bool)
      , Binding (Name "minus") (Function [Integer, Integer] Integer)
      , Binding (Name "plus") (Function [Integer, Integer] Integer)
      , Binding (Name "str_concat") (Function [String, String] String)
      , Binding (Name "to_string") (Function [Integer] String)
      , Binding (Name "print") (Function [String] Unit)
      ]

main :: IO ()
main = do
  print $ runTypeCheck (checkModule example) defaultContext