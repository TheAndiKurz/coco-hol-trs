{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE DoAndIfThenElse      #-}

module TRS where
import Data.List (nub, sort)
import Data.Foldable (find)
import Control.Monad (zipWithM, foldM)
import Control.Monad.State
import qualified Data.Map as Map
import Utils
import qualified SMT as Smt

newtype Id = Id String deriving (Eq, Ord)

data Sort     = Sort Id deriving (Eq, Ord)
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
  , file_name :: String
  }

instance Show HOLSystem where
    show (HOLSystem sorts functions rules _) = 
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

flagsCombine :: Flags -> Flags -> Flags
flagsCombine (Flags ll1 so1 dhs1 prs1) (Flags ll2 so2 dhs2 prs2) = Flags (ll1 && ll2) (so1 && so2) (dhs1 && dhs2) (prs1 && prs2)

flagsNotLeftLinear :: Flags
flagsNotLeftLinear = Flags {left_linear=False, second_order=True, deterministic_pattern=True, pattern=True}
 
sortId :: Sort -> Id
sortId (Sort id) = id

varId :: Var -> Id
varId (Var id _) = id

varType :: Var -> Type
varType (Var _ t) = t

typeArgs :: Type -> [Type]
typeArgs (Type args _) = args

checkSystem :: HOLSystem -> Either String (Flags, [Var])
checkSystem system = do
    flags <- checkSorts system
    flags' <- checkFunctions system
    flags'' <- checkRules system
    Right ( flagsCombine flags $ flagsCombine flags' flags''
          , filter (not . \var -> any (varUsedInRule var) (rules system)) (functions system)
          )

checkSorts :: HOLSystem -> Either String Flags
checkSorts system = case firstDuplicate (sorts system) of 
    Nothing -> Right $ Flags {left_linear=True, second_order=True, deterministic_pattern=True, pattern=True}
    Just (Sort id) -> Left $ "duplicate sort name: " ++ show id

checkFunctions :: HOLSystem -> Either String Flags
checkFunctions system = do
    order <- checkVars "function" system (functions system)
    return $ Flags {left_linear=True, second_order=(order <= 3), deterministic_pattern=True, pattern=True}

checkRules :: HOLSystem -> Either String Flags
checkRules system = do 
  flags <- mapM (checkRule system) $ rules system
  return $ foldr flagsCombine (Flags {left_linear=True, second_order=True, deterministic_pattern=True, pattern=True}) flags

checkRule :: HOLSystem -> Rule -> Either String Flags
checkRule _ rule@(Rule (TermLambda _ _) _) = Left $
    "rule '" ++ show rule ++ "' has a lambda term in left-hand side"

checkRule system (Rule ruleLeft ruleRight) = do
    typ@(Type _ _) <- getTermType system (functions system) ruleLeft
    (freeVarsL, flags) <- typeCheckWithFreeVariables system False [] [] ruleLeft typ
    (freeVarsL, flags') <- checkFreeVars freeVarsL
    (freeVarsR, flags'') <- typeCheckWithFreeVariables system True freeVarsL [] ruleRight typ
    if length freeVarsR == 0
    then return $ foldl flagsCombine flags [flags', flags'']
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
typeCheckWithFreeVariables :: HOLSystem -> Bool -> [Var] -> [Var] -> Term -> Type -> Either String ([Var], Flags)
typeCheckWithFreeVariables system rhs bound_vars free_vars term@(Term fid args) typ@(Type targs tid) = case findVar (functions system ++ bound_vars) fid of
    -- function application type checking
    Just (Var _ (Type fargs ftid)) | length fargs == length args -> do
        if not $ sameTypes (drop (length args) fargs) targs && ftid == tid
        then Left $ "term '" ++ show term ++ "' does not have type " ++ show typ
        else do
            foldM f
                ([], Flags {left_linear=True, second_order=True, deterministic_pattern=True, pattern=True}) 
                (zip args fargs)
                where 
                    f :: ([Var], Flags) -> (Term, Type) -> Either String ([Var], Flags)
                    f (new_free_vars_acc, flags) (term, typ) = do
                        (new_free_vars, new_flags) <- typeCheckWithFreeVariables system rhs bound_vars (free_vars ++ new_free_vars_acc) term typ
                        return (new_free_vars_acc ++ new_free_vars, flagsCombine flags new_flags)

    Just (Var _ ft@(Type fargs _)) | length fargs == (length args + length targs) ->
        if ft == typ then
            Left $ "term '" ++ show term ++ "' does have expected type (" ++ show typ ++ "), but it is not in expanded eta long normal form and therefore rejected."
        else Left $ "term '" ++ show term ++ "' has type " ++ show ft ++ " which is not the expected type " ++ show typ ++ " and it is not in eta normal form."

    -- free variable type inference
    Nothing | rhs -> Left $ "free variable '" ++ show term ++ "' in right hand side of a rule is not allowed."
    -- NOTE: remove this case for well-behaved?
    Nothing | length targs /= 0 -> Left $ "free variable '" ++ show term ++ "' is not in eta long form."
    Nothing -> do
        -- fails if the argument is a free variable again, because this cannot infer the type then
        term_types <- case findVar free_vars fid of 
            Nothing -> mapM (getTermType system (bound_vars ++ free_vars)) args
            Just var -> Right $ typeArgs $ varType var
        let new_var_type = Type term_types tid
        let new_var_order = typeOrder new_var_type 
        let new_var = Var fid new_var_type

        (varss, flagss) <- unzip <$> zipWithM (typeCheckWithFreeVariables system rhs bound_vars (free_vars ++ [new_var])) args term_types
        let free_vars = concat varss

        let base_flags = Flags { left_linear=True
                               , second_order=new_var_order <= 2
                               , deterministic_pattern=checkDeterministicPattern system bound_vars args
                               , pattern=checkPattern bound_vars args
                               }

        let flags = foldr (flagsCombine) base_flags flagss
        Right $ (new_var : free_vars, flags)

    _ -> Left ("term '" ++ show term ++ "' does not have type " ++ show typ)

typeCheckWithFreeVariables system rhs bound_vars free_vars (TermLambda new_bound_vars body) (Type targs tid)
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
            (vars, flags) <- typeCheckWithFreeVariables system rhs (bound_vars ++ new_bound_vars) free_vars body body_type
            return $ (vars, flagsCombine flags base_flags)
        else Left ("lambda function with wrong variable types. Expected " ++ show targs ++ " but got " ++ show (map varType new_bound_vars))

checkVars :: String -> HOLSystem -> [Var] -> Either String Order
checkVars desc system vars = case firstDuplicate vars of
    Just (Var id _) -> Left $ "every " ++ desc ++ " has to have a unique name and cannot be shadowed. Duplicated variable name: " ++ show id
    Nothing -> foldM (\order var -> (max order) <$> checkType system (varType var)) 1 $ functions system

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

typeFlatten :: Type -> [Sort]
typeFlatten (Type [] s) = [Sort s]
typeFlatten (Type args s) = concatMap typeFlatten args ++ [Sort s]


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
preProcessSystemDuplicates :: HOLSystem -> (HOLSystem, [[Var]])
preProcessSystemDuplicates system = 
    let system' = alphaNormalizeRules $ removeUnused system in
    (system', varsDevideIntoTypeClasses $ functions system')

duplicate :: String -> (HOLSystem, [[Var]]) -> (HOLSystem, [[Var]]) -> IO Bool
duplicate tool (system1, type_classes1) (system2, type_classes2) = do
    if length (functions system1) /= length (functions system2) ||
       length (sorts system1) /= length (sorts system2) || 
       length type_classes1 /= length type_classes2
    then return False else do

    case groupTypeClasses type_classes1 type_classes2 of
        Nothing -> return False -- some type_class in first system does not match any other type_class in the other system
        Just function_groups -> do 
            let commands = sortSmt (sorts system1) (sorts system2) 
                           ++ functionsSmt function_groups 
                           ++ [rulesSmt (rules system1) (rules system2)]
            -- putStr $ Smt.showSmtInput commands
            Smt.check_sat tool commands

removeUnused :: HOLSystem -> HOLSystem
removeUnused (HOLSystem {sorts=_sorts, functions=_functions, rules=_rules, file_name=_file_name}) =
    let 
        filtered_functions = [function | function <- _functions, any (varUsedInRule function) _rules]
        filtered_sorts = [sort | sort <- _sorts, any (sortUsedInType sort) $ map varType filtered_functions]
    in 
    HOLSystem { sorts=filtered_sorts
              , functions=filtered_functions
              , rules=nub _rules
              , file_name=_file_name
              }

alphaNormalizeRules :: HOLSystem -> HOLSystem
alphaNormalizeRules HOLSystem {sorts=_sorts, functions=_functions, rules=_rules, file_name=_file_name} = 
    HOLSystem { sorts=_sorts
              , functions=_functions
              , rules=map (alphaNormalizeRule (\id -> not (elem id $ map varId _functions))) _rules
              , file_name=_file_name
              }

data RenameState = RenameState 
    { freeVars   :: Map.Map Id Id  -- Maps original free Id to (x_i)
    , freeCount  :: Int            -- Counter for (x_i)
    , boundCount :: Int            -- Counter for (z_i)
    }


-- renames free variables to (x_i) and bound variables to (z_i)
-- including the "()" into this, because parsing this is not allowed and 
-- checking if it is a variable later is therefore trivial
alphaNormalizeRule :: (Id -> Bool) -> Rule -> Rule
alphaNormalizeRule isVar (Rule lhs rhs) = 
    evalState (do
      lhs' <- renameTerm isVar Map.empty lhs
      rhs' <- renameTerm isVar Map.empty rhs
      return $ Rule lhs' rhs'
    ) (RenameState Map.empty 1 1)
    where 
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
            
            let newId = Id ("(z_" ++ show c ++ ")")
            let newVar = Var newId typ 
            return (newVar : accVars, Map.insert oldId newId env)
        
        getFreeVar :: Id -> State RenameState Id
        getFreeVar oldId = do
            st <- get
            case Map.lookup oldId (freeVars st) of
                Just newId -> return newId
                Nothing -> do
                    let c = freeCount st
                    let newId = Id ("(x" ++ show c ++ ")")
                    put st { freeCount = c + 1
                           , freeVars = Map.insert oldId newId (freeVars st) 
                           }
                    return newId

varsDevideIntoTypeClasses :: [Var] -> [[Var]]
varsDevideIntoTypeClasses vars = 
    let 
        insertVar :: Var -> [[Var]] -> [[Var]]
        insertVar _ ([] : _) = error "there cannot be an empty type_class"
        insertVar new_var (type_class@(rep : _) : rest_classes)
            | typeSameSkeleton (varType new_var) (varType rep) = (new_var : type_class) : rest_classes
            | otherwise = type_class : insertVar new_var rest_classes
        insertVar new_var [] = [[new_var]]
    in
    foldr insertVar [] vars

groupTypeClasses :: [[Var]] -> [[Var]] -> Maybe [([Var], [Var])]
groupTypeClasses [] [] = Just []
groupTypeClasses [] _ = Nothing
groupTypeClasses (c1@(v1:_):restClasses1) classes2 =
    let 
        isMatch :: [Var] -> Bool
        isMatch (v2:_) = typeSameSkeleton (varType v1) (varType v2)
        isMatch []     = False
        
        extractMatch :: [[Var]] -> (Maybe [Var], [[Var]])
        extractMatch [] = (Nothing, [])
        extractMatch (x:xs)
            | isMatch x = (Just x, xs)
            | otherwise = let (m, rest) = extractMatch xs in (m, x : rest)
            
        (matchedClass, remainingClasses2) = extractMatch classes2
    in case matchedClass of
        Just c2 -> (:) (c1, c2) <$> groupTypeClasses restClasses1 remainingClasses2
        Nothing -> Nothing

groupTypeClasses ([]:_) _ = error "there cannot be an empty type_class"

typeSameSkeleton :: Type -> Type -> Bool
typeSameSkeleton (Type args1 _) (Type args2 _)
    | length args1 /= length args2 = False
    | otherwise = all id $ zipWith typeSameSkeleton args1 args2

-- Smt
var1 :: Id -> String -> String
var1 id typ = "x_" ++ typ ++ "_" ++ show id

var2 :: Id -> String -> String
var2 id typ = "y_" ++ typ ++ "_" ++ show id

sortEq :: Sort -> Sort -> Smt.Formula
sortEq (Sort id1) (Sort id2) = Smt.Eq (Smt.Var $ var1 id1 "s") (Smt.Var $ var2 id2 "s")

sortSmt :: [Sort] -> [Sort] -> [Smt.Command]
sortSmt sorts1 sorts2 = declarations1 ++ declarations2 ++ [distinct_sorts1, distinct_sorts2, one_match]
  where
    declarations1 = [ Smt.DeclareInt $ var1 id "s" | Sort id <- sorts1 ]
    declarations2 = [ Smt.DeclareInt $ var2 id "s" | Sort id <- sorts2 ]
    
    distinct_sorts1 = Smt.Assert $ Smt.Distinct [Smt.Var $ var1 id "s" | Sort id <- sorts1]
    distinct_sorts2 = Smt.Assert $ Smt.Distinct [Smt.Var $ var2 id "s" | Sort id <- sorts2]

    one_match = Smt.Assert $ 
        Smt.conj [ Smt.disj [ sortEq sort1 sort2 | sort2 <- sorts2 ]
                 | sort1 <- sorts1
                 ]
functionsSmt :: [([Var],[Var])] -> [Smt.Command]
functionsSmt [] = []
functionsSmt ((funs1, funs2):rest) = declerations1 ++ declerations2 ++ [distinct_funs1, distinct_funs2, one_match] ++ functionsSmt rest
  where
    declerations1 = [ Smt.DeclareInt $ var1 id "f" | Var id _ <- funs1]
    declerations2 = [ Smt.DeclareInt $ var2 id "f" | Var id _ <- funs2]
    
    distinct_funs1 = Smt.Assert $ Smt.Distinct [Smt.Var $ var1 id "f" | Var id _ <- funs1]
    distinct_funs2 = Smt.Assert $ Smt.Distinct [Smt.Var $ var2 id "f" | Var id _ <- funs2]

    functionEq :: Var -> Var -> Smt.Formula
    functionEq (Var id1 typ1) (Var id2 typ2) = Smt.conj $
        Smt.Eq (Smt.Var $ var1 id1 "f") (Smt.Var $ var2 id2 "f") : zipWith sortEq (typeFlatten typ1) (typeFlatten typ2) 

    one_match = Smt.Assert $
        Smt.conj [Smt.disj [ functionEq fun1 fun2 | fun2 <- funs2 ] 
                 | fun1 <- funs1
                 ]

isVariable :: Id -> Bool
isVariable id
    | take 1 (show id) == "(" = True
    | otherwise = False

termsEq :: Term -> Term -> Smt.Formula
termsEq (Term tid1 args1) (Term tid2 args2) 
    | isVariable tid1 && isVariable tid2 = Smt.conj argsEq
    | not (isVariable tid1 || isVariable tid2) = Smt.conj $ funEq : argsEq
    | otherwise = Smt.bottom
    where argsEq = zipWith termsEq args1 args2
          funEq = Smt.Eq (Smt.Var $ var1 tid1 "f") (Smt.Var $ var2 tid2 "f")

termsEq (TermLambda _ body1) (TermLambda _ body2) = termsEq body1 body2
termsEq _ _ = Smt.bottom

rulesSmt :: [Rule] -> [Rule] -> Smt.Command
rulesSmt rules1 rules2 = Smt.Assert $ 
    Smt.conj [ 
        Smt.disj [
            Smt.conj [ termsEq lhs1 lhs2, termsEq rhs1 rhs2 ] 
        | Rule lhs2 rhs2 <- rules2 ] 
    | Rule lhs1 rhs1 <- rules1 ] 
