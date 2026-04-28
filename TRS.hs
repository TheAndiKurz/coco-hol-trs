module TRS where
import Data.List (nub, sort)
import Data.Foldable (find)
import Control.Monad (zipWithM, foldM)
import Data.Either (isRight)

newtype Id = Id String deriving (Eq, Ord)

data Sort     = Sort Id deriving Eq
data Type     = Type [Type] Id deriving Eq
data Var      = Var Id Type
data Term     = Term Id [Term] | TermLambda [Var] Term deriving Eq

data Rule = Rule Term Term

instance Show Id where
    show (Id id) = id

instance Show Sort where
    show (Sort id) = "(sort " ++ show id ++ ")"

instance Show Type where
  show (Type [] id) = show id
  show (Type args id) = "(->" ++ concatMap ((" " ++) . show) args ++ " " ++ show id ++ ")"

instance Show Var where
  show (Var id typ) = "(" ++ show id ++ " " ++ show typ ++ ")"

instance Show Term where
  show (Term id []) = show id
  show (Term id args) = "(" ++ show id ++ concatMap ((" " ++) . show) args ++ ")"
  show (TermLambda vars t) = "(lambda ( " ++ concatMap ((++ " ") . show) vars ++ ") " ++ show t ++ ")"

instance Show Rule where
  show (Rule t1 t2) = "(rule " ++ show t1 ++ " " ++ show t2 ++ ")"

data HOLSystem = HOLSystem
  { sorts     :: [Sort]
  , functions :: [Var]
  , rules     :: [Rule]
  }

instance Show HOLSystem where
    show (HOLSystem sorts functions rules) = 
      unlines $ (map show sorts) ++ (map show functions) ++ (map show rules)

type Order = Int
type Second_Order = Bool
type Left_Linear = Bool
type Pattern = Bool
type Deterministic_Pattern = Bool

data Flags = Flags 
  { left_linear :: Left_Linear
  , second_order :: Second_Order
  , deterministic_pattern :: Deterministic_Pattern
  , pattern :: Pattern
  } deriving Show

instance Eq Var where
    (Var id1 _) == (Var id2 _) = id1 == id2

instance Ord Var where
    compare (Var id1 _) (Var id2 _) = compare id1 id2


combineFlags :: Flags -> Flags -> Flags
combineFlags (Flags ll1 so1 dhs1 prs1) (Flags ll2 so2 dhs2 prs2) = Flags (ll1 && ll2) (so1 && so2) (dhs1 && dhs2) (prs1 && prs2)
 
sortId :: Sort -> Id
sortId (Sort id) = id

varId :: Var -> Id
varId (Var id _) = id

varType :: Var -> Type
varType (Var _ t) = t


checkSystem :: HOLSystem -> Either String (Flags, []Var)
checkSystem system = do
    flags <- checkSorts system
    flags' <- checkFunctions system
    flags'' <- checkRules system
    Right ( combineFlags flags $ combineFlags flags' flags''
          , filter (not . \var -> any (varUsedInRule var) (rules system)) (functions system)
          )

checkSorts :: HOLSystem -> Either String Flags
-- TODO: show name of duplicate sorts
checkSorts system
    | length (sorts system) /= length (nub $ sorts system) =
        Left ("every sort has to have a unique name")
    | otherwise = Right $ Flags {left_linear=True, second_order=True, deterministic_pattern=True, pattern=True}

checkFunctions :: HOLSystem -> Either String Flags
checkFunctions system = do
    order <- checkVars "function" system (functions system)
    return $ Flags {left_linear=True, second_order=(order <= 3), deterministic_pattern=True, pattern=True}

checkRules :: HOLSystem -> Either String Flags
checkRules system = do 
  flags <- mapM (checkRule system) $ rules system
  return $ foldr combineFlags (Flags {left_linear=True, second_order=True, deterministic_pattern=True, pattern=True}) flags

checkRule :: HOLSystem -> Rule -> Either String Flags
checkRule _ rule@(Rule (TermLambda _ _) _) = Left $
    "rule '" ++ show rule ++ "' has a lambda term in left-hand side"

checkRule system (Rule ruleLeft ruleRight) = do
    typ@(Type args _) <- getTermType system (functions system) ruleLeft
    (freeVarsL, flags) <- typeCheckWithFreeVariables system (functions system) ruleLeft typ
    (freeVarsL, flags') <- checkFreeVars freeVarsL
    (freeVarsR, flags'') <- typeCheckWithFreeVariables system (functions system ++ freeVarsL) ruleRight typ
    if length freeVarsR == 0
    then return $ combineFlags flags $ combineFlags flags' flags''
    else Left $ "rule '" ++ show (ruleLeft, ruleRight)
        ++ "' has free variables in right hand side that do not appear in left-hand side: "
        ++ show freeVarsR

checkFreeVars :: [Var] -> Either String ([Var], Flags)
checkFreeVars vars = do
  (vars, left_linear, order) <- check $ sort vars
  return $ (vars, Flags {left_linear=left_linear, second_order=order <= 2, deterministic_pattern=True, pattern=True})
    where
        check :: [Var] -> Either String ([Var], Left_Linear, Order)
        check (v1@(Var _ typ) : v2 : vs)
            | varId v1 == varId v2 && varType v1 /= varType v2 = Left $
                "free variable '" ++ show v1 ++ "' occures twice and has different types: "
                ++ show (varType v1) ++ " and " ++ show (varType v2)
            | varId v1 == varId v2 = do 
                (vs, _, order) <- check (v2 : vs)
                return $ (vs, False, max order $ typeOrder typ)
            | otherwise = do 
                (vs, ll, order) <- check (v2 : vs)
                return $ (v1 : vs, ll, max order $ typeOrder typ)
        check [v@(Var _ typ)] = Right ([v], True, typeOrder typ)
        check [] = Right ([], True, 1)

varUsedInRule :: Var -> Rule -> Bool
varUsedInRule var (Rule t1 t2) = varUsedInTerm var t1 || varUsedInTerm var t2

varUsedInTerm :: Var -> Term -> Bool
varUsedInTerm var (TermLambda _ body) = varUsedInTerm var body
varUsedInTerm var@(Var vid _) (Term tid args) 
    | vid == tid = True
    | otherwise = any (varUsedInTerm var) args

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
typeCheckWithFreeVariables :: HOLSystem -> [Var] -> Term -> Type -> Either String ([Var], Flags)
typeCheckWithFreeVariables system vars term@(Term fid args) typ@(Type targs tid) = case findVar vars fid of
    -- function application type checking
    Just (Var _ ft@(Type fargs ftid)) | length fargs == length args -> do
        if not $ sameTypes (drop (length args) fargs) targs && ftid == tid
        then Left ("term '" ++ show term ++ "' does not have type " ++ show typ)
        else do
            (varss, flags) <- unzip <$> zipWithM (typeCheckWithFreeVariables system vars) args fargs
            Right $ (concat varss, foldr (combineFlags) (Flags {left_linear=True, second_order=True, deterministic_pattern=True, pattern=True}) flags)

    Just (Var _ ft@(Type fargs ftid)) | length fargs == (length args + length targs) ->
        Left $ "term '" ++ show term ++ "' does have expected type (" ++ show typ ++ "), but it is not in expanded eta long normal form and therefore rejected."

    -- free variable type inference
    -- NOTE: remove this case for well-behaved?
    Nothing | length targs /= 0 -> Left $ "free variable '" ++ show term ++ "' is not in eta long form."
    Nothing -> do
        -- fails if the argument is a free variable again, because this cannot infer the type then
        termTypes <- mapM (getTermType system vars) args
        let newVarType = Type (termTypes ++ targs) tid
        let newVarOrder = typeOrder newVarType 
        let newVar = Var fid newVarType

        (varss, flagss) <- unzip <$> zipWithM (typeCheckWithFreeVariables system vars) args termTypes
        let freeVars = concat varss
        let baseFlags = Flags { left_linear=True
                              , second_order=newVarOrder <= 2
                              , deterministic_pattern=True
                              , pattern=(length args == length (nub args))
                              }
        let flags = foldr (combineFlags) baseFlags flagss
        Right $ (newVar : freeVars, flags)

    _ -> Left ("term '" ++ show term ++ "' does not have type " ++ show typ)

typeCheckWithFreeVariables system vars (TermLambda newVars body) t@(Type targs tid)
    | length newVars > length targs = Left $
        "lambda function with more variables then expected. Expected at most "
        ++ show (length targs) ++ " but got " ++ show (length newVars)
    | otherwise = do
        -- no shadowing and no duplicates
        checkVars "lambda function variable" system (vars ++ newVars)

        let maxOrder = maximum $ map (typeOrder . varType) newVars
        let baseFlags = Flags {left_linear=True, second_order=maxOrder <= 1, deterministic_pattern=True, pattern=True}
        -- expected type of the body
        let bodyType = Type (drop (length newVars) targs) tid
        if sameTypes (map varType newVars) (take (length newVars) targs)
        then do 
            (vars, flags)<- typeCheckWithFreeVariables system (vars ++ newVars) body bodyType
            return $ (vars, combineFlags flags baseFlags)
        else Left ("lambda function with wrong variable types. Expected " ++ show targs ++ " but got " ++ show (map varType newVars))

checkVars :: String -> HOLSystem -> [Var] -> Either String Order
-- TODO: show name of duplicate vars
checkVars desc system vars
    | length vars /= length (nub vars) = Left ("every "++ desc ++" has to have a unique name and cannot be shadowed")
    | otherwise = foldM (\order var -> (max order) <$> checkType system (varType var)) 1 $ functions system

sameTypes :: [Type] -> [Type] -> Bool
sameTypes ts1 ts2
  | length ts1 /= length ts2 = False
  | otherwise = all (\(t1, t2) -> t1 == t2) $ zip ts1 ts2

findVar :: [Var] -> Id -> Maybe Var
findVar vars id = find ((==) id . varId) $ vars

checkType :: HOLSystem -> Type -> Either String Order
checkType system (Type [] ret) =
    if ret `elem` (map sortId $ sorts system)
    then Right 1
    else Left ("sort '" ++ show ret ++ "' is not defined")

checkType system (Type args ret) = do
    orders <- mapM (checkType system) args
    return $ 1 + maximum orders

typeOrder :: Type -> Order
typeOrder (Type [] ret) = 1
typeOrder (Type types ret) = 1 + (maximum $ map typeOrder types)
