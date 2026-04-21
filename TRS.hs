module TRS where
import Data.List (nub, sort)
import Data.Foldable (find)
import Control.Monad (zipWithM)
import Debug.Trace (traceM)

newtype Id = Id String deriving (Show, Eq, Ord)

data Sort     = Sort Id deriving (Show, Eq)
data Type     = Type [Type] Id deriving (Show, Eq)
data Var      = Var Id Type deriving Show
data Term     = Term Id [Term] | TermLambda [Var] Term deriving Show

data HOLSystem = HOLSystem
  { sorts     :: [Sort]
  , functions :: [Var]
  , rules     :: [(Term, Term)]
  } deriving Show

instance Eq Var where
    (Var id1 _) == (Var id2 _) = id1 == id2

instance Ord Var where
    compare (Var id1 _) (Var id2 _) = compare id1 id2

sortId :: Sort -> Id
sortId (Sort id) = id

varId :: Var -> Id
varId (Var id _) = id

varType :: Var -> Type
varType (Var _ t) = t

checkSystem :: HOLSystem -> Either String ()
checkSystem system = do
    checkSorts system
    checkFunctions system
    checkRules system
    Right ()

checkSorts :: HOLSystem -> Either String ()
-- TODO: show name of duplicate sorts
checkSorts system
    | length (sorts system) /= length (nub $ sorts system) =
        Left ("every sort has to have a unique name")
    | otherwise = Right ()

checkFunctions :: HOLSystem -> Either String ()
checkFunctions system = checkVars "function" system (functions system)

checkRules :: HOLSystem -> Either String ()
checkRules system = mapM_ (checkRule system) $ rules system

checkRule :: HOLSystem -> (Term, Term) -> Either String ()
checkRule _ rule@((TermLambda _ _), _) = Left $
    "rule " ++ show rule ++ " has a lambda term in left-hand side"

checkRule system (ruleLeft, ruleRight) = do
    typ@(Type args _) <- getTermType system (functions system) ruleLeft
    traceM $ "type: " ++ show typ
    freeVarsL <- typeCheckWithFreeVariables system (functions system) ruleLeft typ
    freeVarsL <- checkFreeVars freeVarsL
    freeVarsR <- typeCheckWithFreeVariables system (functions system ++ freeVarsL) ruleRight typ
    if length freeVarsR == 0
    then return ()
    else Left $ "rule " ++ show (ruleLeft, ruleRight)
        ++ " has free variables in right hand side that do not appear in left-hand side: "
        ++ show freeVarsR

checkFreeVars :: [Var] -> Either String [Var]
checkFreeVars vars = check $ sort vars
    where
        check :: [Var] -> Either String [Var]
        check (v1 : v2 : vs)
            | varId v1 == varId v2 && varType v1 /= varType v2 = Left $
                "free variable '" ++ show v1 ++ "' occures twice and has different types: "
                ++ show (varType v1) ++ " and " ++ show (varType v2)
            | varId v1 == varId v2 = check (v2 : vs)
            | otherwise = (:) v1 <$> check (v2 : vs)
        check vs = Right vs

getTermType :: HOLSystem -> [Var] -> Term -> Either String Type
getTermType system vars term@(Term id args) = case findVar vars id of
    Just (Var _ (Type fargs _)) | length fargs /= length args ->
        Left $ "function '" ++ show id ++ "' expects " ++ show (length fargs)
            ++ " arguments, but got " ++ show (length args) ++ "."

    Just (Var _ (Type fargs ret)) -> Right $ Type (drop (length args) fargs) ret
    Nothing -> getTermTypeFreeVariableError term

getTermType system vars (TermLambda newVars body) = do
    -- no shadowing and no duplicates allowed
    checkVars "variable" system (vars ++ newVars)

    let newVarTypes = map varType newVars
    (Type bargs ret) <- getTermType system (vars ++ newVars) body
    return $ Type (newVarTypes ++ bargs) ret

getTermTypeFreeVariableError :: Term -> Either String Type
getTermTypeFreeVariableError term = Left $
    "free variable '" ++ show term ++ "' cannot get infered with this scope. Maybe it is a free variable as direct argument of an application of a free variable or it is the root of a rule?"


-- expect a type for a term to typecheck the term.
-- On success returns free variables with inferred type
typeCheckWithFreeVariables :: HOLSystem -> [Var] -> Term -> Type -> Either String [Var]
typeCheckWithFreeVariables system vars term@(Term fid args) typ@(Type targs tid) = case findVar vars fid of
    -- function application type checking
    Just (Var _ ft@(Type fargs ftid)) | length fargs == length args -> do
        if not $ sameTypes (drop (length args) fargs) targs && ftid == tid
        then Left ("term '" ++ show term ++ "' does not have type " ++ show typ)
        else do
            freeVars <- concat <$> zipWithM (typeCheckWithFreeVariables system vars) args fargs
            Right $ freeVars

    Just (Var _ ft@(Type fargs ftid)) | length fargs == (length args + length targs) ->
        Left $ "term '" ++ show term ++ "' does have expected type (" ++ show typ ++ "), but it is not in expanded eta long normal form and therefore rejected."

    -- free variable type inference
    Nothing -> do
        -- fails if the argument is a free variable again, because this cannot infer the type then
        termTypes <- mapM (getTermType system vars) args
        freeVars <- concat <$> zipWithM (typeCheckWithFreeVariables system vars) args termTypes
        Right $ (Var fid $ Type (termTypes ++ targs) tid) : freeVars

    _ -> Left ("term '" ++ show term ++ "' does not have type " ++ show typ)

typeCheckWithFreeVariables system vars (TermLambda newVars body) t@(Type targs tid)
    | length newVars > length targs = Left $
        "lambda function with more variables then expected. Expected at most "
        ++ show (length targs) ++ " but got " ++ show (length newVars)
    | otherwise = do
        -- no shadowing and no duplicates
        checkVars "lambda function variable" system (vars ++ newVars)
        -- expected type of the body
        let bodyType = Type (drop (length newVars) targs) tid
        if sameTypes (map varType newVars) (take (length newVars) targs)
        then do typeCheckWithFreeVariables system (vars ++ newVars) body bodyType
        else Left ("lambda function with wrong variable types. Expected " ++ show targs ++ " but got " ++ show (map varType newVars))


checkVars :: String -> HOLSystem -> [Var] -> Either String ()
-- TODO: show name of duplicate vars
checkVars desc system vars
    | length vars /= length (nub vars) = Left ("every "++ desc ++" has to have a unique name and cannot be shadowed")
    | otherwise = mapM_ (checkType system . varType) $ functions system

sameTypes :: [Type] -> [Type] -> Bool
sameTypes ts1 ts2
  | length ts1 /= length ts2 = False
  | otherwise = all (\(t1, t2) -> t1 == t2) $ zip ts1 ts2

findVar :: [Var] -> Id -> Maybe Var
findVar vars id = find ((==) id . varId) $ vars

checkType :: HOLSystem -> Type -> Either String ()
checkType system (Type [] ret) =
    if ret `elem` (map sortId $ sorts system)
    then Right ()
    else Left ("sort '" ++ show ret ++ "' is not defined")

checkType system (Type (arg:args) ret) = do
    checkType system arg
    checkType system (Type args ret)
