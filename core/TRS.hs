{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE DoAndIfThenElse      #-}

module TRS where
import Data.List (nub, sort)
import Data.Foldable (find)
import Control.Monad (zipWithM, foldM)
import Control.Monad.State
import qualified Data.Map as Map
import Debug.Trace (trace)

newtype Id = Id String deriving (Eq, Ord)

data Sort     = Sort Id deriving Eq
data Type     = Type [Type] Id deriving Eq
data Var      = Var Id Type
data Term     = Term Id [Term] | TermLambda [Var] Term deriving Eq

data Rule = Rule Term Term deriving Eq

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

checkSystem :: HOLSystem -> Either String (Flags, [Var])
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
    typ@(Type _ _) <- getTermType system (functions system) ruleLeft
    (freeVarsL, flags) <- typeCheckWithFreeVariables system [] ruleLeft typ
    (freeVarsL, flags') <- checkFreeVars freeVarsL
    (freeVarsR, flags'') <- typeCheckWithFreeVariables system freeVarsL ruleRight typ
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

sortUsedInType :: Sort -> Type -> Bool
sortUsedInType s@(Sort sort_id) (Type args type_id) = sort_id == type_id || any (sortUsedInType s) args

varUsedInRule :: Var -> Rule -> Bool
varUsedInRule var (Rule t1 t2) = varUsedInTerm var t1 || varUsedInTerm var t2

varUsedInTerm :: Var -> Term -> Bool
varUsedInTerm var (TermLambda _ body) = varUsedInTerm var body
varUsedInTerm var@(Var vid _) (Term tid args) 
    | vid == tid = True
    | otherwise = any (varUsedInTerm var) args

getTermType :: HOLSystem -> [Var] -> Term -> Either String Type
getTermType system bound_vars term@(Term id args) = case findVar (functions system ++ bound_vars) id of
    Just (Var _ (Type fargs _)) | length fargs /= length args ->
        Left $ "function '" ++ show id ++ "' expects " ++ show (length fargs)
            ++ " arguments, but got " ++ show (length args) ++ "."

    Just (Var _ (Type fargs ret)) -> Right $ Type (drop (length args) fargs) ret
    Nothing -> getTermTypeFreeVariableError term

getTermType system vars (TermLambda newVars body) = do
    -- no shadowing and no duplicates allowed
    _ <- checkVars "variable" system (vars ++ newVars)

    let newVarTypes = map varType newVars
    (Type bargs ret) <- getTermType system (vars ++ newVars) body
    return $ Type (newVarTypes ++ bargs) ret

getTermTypeFreeVariableError :: Term -> Either String Type
getTermTypeFreeVariableError term = Left $
    "free variable '" ++ show term ++ "' cannot get infered with this scope. Maybe it is a free variable as direct argument of an application of a free variable or it is the root of a rule?"


-- expect a type for a term to typecheck the term.
-- On success returns free variables with inferred type
typeCheckWithFreeVariables :: HOLSystem -> [Var] -> Term -> Type -> Either String ([Var], Flags)
typeCheckWithFreeVariables system bound_vars term@(Term fid args) typ@(Type targs tid) = case findVar (functions system ++ bound_vars) fid of
    -- function application type checking
    Just (Var _ (Type fargs ftid)) | length fargs == length args -> do
        if not $ sameTypes (drop (length args) fargs) targs && ftid == tid
        then Left $ "term '" ++ show term ++ "' does not have type " ++ show typ
        else do
            (varss, flags) <- unzip <$> zipWithM (typeCheckWithFreeVariables system bound_vars) args fargs
            Right $ (concat varss, foldr (combineFlags) (Flags {left_linear=True, second_order=True, deterministic_pattern=True, pattern=True}) flags)

    Just (Var _ ft@(Type fargs _)) | length fargs == (length args + length targs) ->
        if ft == typ then
            Left $ "term '" ++ show term ++ "' does have expected type (" ++ show typ ++ "), but it is not in expanded eta long normal form and therefore rejected."
        else Left $ "term '" ++ show term ++ "' has type " ++ show ft ++ " which is not the expected type " ++ show typ ++ " and it is not in eta normal form."

    -- free variable type inference
    -- NOTE: remove this case for well-behaved?
    Nothing | length targs /= 0 -> Left $ "free variable '" ++ show term ++ "' is not in eta long form."
    Nothing -> do
        -- fails if the argument is a free variable again, because this cannot infer the type then
        term_types <- mapM (getTermType system bound_vars) args
        let new_var_type = Type (term_types ++ targs) tid
        let new_var_order = typeOrder new_var_type 
        let new_var = Var fid new_var_type

        (varss, flagss) <- unzip <$> zipWithM (typeCheckWithFreeVariables system bound_vars) args term_types
        let free_vars = concat varss

        let base_flags = Flags { left_linear=True
                               , second_order=new_var_order <= 2
                               , deterministic_pattern=checkDeterministicPattern system bound_vars args
                               , pattern=checkPattern bound_vars args
                               }

        let flags = foldr (combineFlags) base_flags flagss
        Right $ (new_var : free_vars, flags)

    _ -> Left ("term '" ++ show term ++ "' does not have type " ++ show typ)

typeCheckWithFreeVariables system bound_vars (TermLambda new_bound_vars body) (Type targs tid)
    | length new_bound_vars > length targs = Left $
        "lambda function with more variables then expected. Expected at most "
        ++ show (length targs) ++ " but got " ++ show (length new_bound_vars)
    | otherwise = do
        -- no shadowing and no duplicates
        _ <- checkVars "lambda function variable" system (bound_vars ++ new_bound_vars)

        let max_order = maximum $ map (typeOrder . varType) new_bound_vars
        let base_flags = Flags {left_linear=True, second_order=max_order <= 1, deterministic_pattern=True, pattern=True}
        -- expected type of the body
        let body_type = Type (drop (length new_bound_vars) targs) tid
        if sameTypes (map varType new_bound_vars) (take (length new_bound_vars) targs)
        then do 
            (vars, flags) <- typeCheckWithFreeVariables system (bound_vars ++ new_bound_vars) body body_type
            return $ (vars, combineFlags flags base_flags)
        else Left ("lambda function with wrong variable types. Expected " ++ show targs ++ " but got " ++ show (map varType new_bound_vars))

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

checkType system (Type args _) = do
    orders <- mapM (checkType system) args
    return $ 1 + maximum orders

typeOrder :: Type -> Order
typeOrder (Type [] _) = 1
typeOrder (Type types _) = 1 + (maximum $ map typeOrder types)


-- DHS Deterministic higher-order rewrite patterns
checkDeterministicPattern :: HOLSystem -> [Var] -> [Term] -> Bool
checkDeterministicPattern system bound_vars args = 
    let 
        defined_ids = map varId $ functions system ++ bound_vars
        eta_reduces_args = map etaReduce args

        containsBoundVar :: [Id] -> Term -> Bool
        containsBoundVar bound_ids term = any (\v -> isFree v term) bound_ids
        
        enumerated_args = zip [0 :: Int ..] eta_reduces_args

        term_pairs :: [(Term, Term)] 
        term_pairs = 
            [ (snd term1, snd term2) 
            | term1 <- enumerated_args
            , term2 <- enumerated_args
            , fst term1 /= fst term2
            ]


        subtermRelation :: Term -> Term -> Bool
        subtermRelation term1 term2
          | term1 == term2 = True
          | otherwise = case term2 of
            (Term _ []) -> False
            (Term term_id term_args) -> 
                subtermRelation term1 (last term_args) ||
                subtermRelation term1 (Term term_id $ init term_args)
            _ -> False

        isLambda :: Term -> Bool
        isLambda (TermLambda _ _) = True
        isLambda _ = False
    in 
    -- every arg has at least one bound var
    all (containsBoundVar (map varId bound_vars)) eta_reduces_args 
    -- all vars are bound by either variable of function symbol
    && all (not . (hasFree defined_ids)) eta_reduces_args
    -- all terms need to be expanded or rather no term can be a lambda after eta reduction
    && all (not . isLambda) eta_reduces_args
    && all (not . (\ (term1, term2) -> subtermRelation term1 term2)) term_pairs


-- PRS pattern rewrite system
checkPattern :: [Var] -> [Term] -> Bool
checkPattern bound_vars args = 
    let eta_reduces_args = map etaReduce args

        termSuitableForPattern :: Term -> Bool  
        termSuitableForPattern (Term tid []) = elem tid (map varId bound_vars)
        termSuitableForPattern _ = False
    in
    all termSuitableForPattern eta_reduces_args
    && (length eta_reduces_args == length (nub eta_reduces_args)) 

etaReduce :: Term -> Term
etaReduce (TermLambda vars1 (TermLambda vars2 t)) = etaReduce (TermLambda (vars1 ++ vars2) t)
etaReduce (TermLambda lambda_vars (Term f args)) =
    let 
        reduceTail :: [Var] -> [Term] -> ([Var], [Term])
        reduceTail (var : vars) ((Term arg_id []) : terms)
            | varId var == arg_id && arg_id /= f && not (any (isFree arg_id) terms) = reduceTail vars terms
        reduceTail vs as = (reverse vs, reverse as)

        (new_vars, new_args) = reduceTail (reverse lambda_vars) (reverse args)
    in 
        if null new_vars
        then Term f new_args
        else TermLambda new_vars (Term f new_args)
etaReduce t = t

isFree :: Id -> Term -> Bool
isFree var_id (Term term_id term_args) = var_id == term_id || any (isFree var_id) term_args
isFree var_id (TermLambda vs body) = var_id `notElem` map varId vs && isFree var_id body

hasFree :: [Id] -> Term -> Bool
hasFree ids (Term term_id term_args) = not (elem term_id ids) || any (hasFree ids) term_args
hasFree ids (TermLambda new_vars body) = hasFree (ids ++ map varId new_vars) body


-- duplicate checking
alphaEqual :: HOLSystem -> HOLSystem -> Bool
alphaEqual system1 system2 =
    let system1' = alphaNormalizeRules system1 in
    let system1 = removeUnused system1' in
    let system2' = alphaNormalizeRules system2 in
    let system2 = removeUnused system2' in

    trace (show system1 ++ show system2)
    False

removeUnused :: HOLSystem -> HOLSystem
removeUnused (HOLSystem {sorts=_sorts, functions=_functions, rules=_rules}) =
    let 
        filtered_functions = [function | function <- _functions, any (varUsedInRule function) _rules]
        filtered_sorts = [sort | sort <- _sorts, any (sortUsedInType sort) $ map varType filtered_functions]
    in 
    HOLSystem { sorts=filtered_sorts
              , functions=filtered_functions
              , rules=nub _rules
              }

alphaNormalizeRules :: HOLSystem -> HOLSystem
alphaNormalizeRules HOLSystem {sorts=_sorts, functions=_functions, rules=_rules} = 
    HOLSystem { sorts=_sorts
              , functions=_functions
              , rules=map (alphaNormalizeRule (\id -> not (elem id $ map varId _functions))) _rules
              }

data RenameState = RenameState 
    { freeVars   :: Map.Map Id Id  -- Maps original free Id to x_i
    , freeCount  :: Int            -- Counter for x_i
    , boundCount :: Int            -- Counter for z_i
    }

alphaNormalizeRule :: (Id -> Bool) -> Rule -> Rule
alphaNormalizeRule isVar (Rule lhs rhs) = 
    let 
        renameTerm :: (Id -> Bool) -> Map.Map Id Id -> Term -> State RenameState Term
        renameTerm isVar boundEnv (Term id args) = do
            newId <- case Map.lookup id boundEnv of
                Just boundId -> return boundId
                Nothing -> 
                    if isVar id 
                    then getFreeVar id
                    else return id
            newArgs <- mapM (renameTerm isVar boundEnv) args
            return $ Term newId newArgs
        
        renameTerm isVar boundEnv (TermLambda vars body) = do
            (newVars, newEnv) <- foldM bindVar ([], boundEnv) vars
            newBody <- renameTerm isVar newEnv body
            return $ TermLambda (reverse newVars) newBody
        
        bindVar :: ([Var], Map.Map Id Id) -> Var -> State RenameState ([Var], Map.Map Id Id)
        bindVar (accVars, env) (Var oldId typ) = do
            st <- get
            let c = boundCount st
            put st { boundCount = c + 1 }
            
            let newId = Id ("z" ++ show c)
            let newVar = Var newId typ 
            return (newVar : accVars, Map.insert oldId newId env)
        
        getFreeVar :: Id -> State RenameState Id
        getFreeVar oldId = do
            st <- get
            case Map.lookup oldId (freeVars st) of
                Just newId -> return newId
                Nothing -> do
                    let c = freeCount st
                    let newId = Id ("x" ++ show c)
                    put st { freeCount = c + 1
                           , freeVars = Map.insert oldId newId (freeVars st) 
                           }
                    return newId
    in
    evalState (do
      lhs' <- renameTerm isVar Map.empty lhs
      rhs' <- renameTerm isVar Map.empty rhs
      return $ Rule lhs' rhs'
    ) (RenameState Map.empty 1 1)

