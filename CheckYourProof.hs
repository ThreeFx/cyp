module CheckYourProof where
import Data.Char
import Control.Monad
import Text.Regex
import Data.List
import Language.Haskell.Exts.Parser 
import Language.Haskell.Exts.Syntax(Literal (..), QName(..), SpecialCon (..), Name (..), ModuleName (..), Exp (..), QOp (..))

{-
Copyright by Dominik Durner / Technische Universität München - Institute for Informatics - Chair for Logic and Verification (I21)

Check Your Proof (CYP)
 What is CYP?
 Check your Proof is a functional program for students to check the correctness of their proofs by induction over simple data structures (e.g. List, Trees)
	noschinl = Wiweni64
-}

type ConstList = [String]
type VariableList = [String]

testread file expression=
    do
       content <- readFile file
       return (matchRegex (mkRegex (expression ++ "(.*?)" ++ expression))((deleteAll content isControl)))

proof file =
	do
		content <- readFile file
		datatype <- getDataType content "<Datatype>"
		sym <- varToConst $ getSym content "<Sym>"
		(func, globalConstList) <- getFunc content "<Def>" sym
		lemmata <- getCyp content "<Lemma>" globalConstList
		induction <- getCyp content "<Induction>" globalConstList
		hypothesis <- getCyp content "<Hypothesis>" globalConstList
		over <- getOver content "<Over>" globalConstList
		proof <- getProof content globalConstList datatype over (func ++ lemmata) induction
		return (proof)
		
		
getProof content globalConstList datatype over rules induction =
    do
        cases <- sequence (map (\x -> getCyp content ("<" ++ fst x ++ ">") globalConstList) datatype)
        proof <- sequence (map (\x -> makeProof induction x over datatype rules) cases)
        return proof

makeProof induction step over datatype rules=
    do
        (newlemma, variable, datatype, static) <- getFirstStep induction step over datatype
        proof <- getSteps (rules ++ newlemma) (map (transformVartoConst) (head step)) (Application (Const "length") (Application (Application (Const ":") (Const "x")) (Const "xs")))
        --ToDo
        return (proof)
        
data Cyp = Application Cyp Cyp | Const String | Variable String | Literal Literal
  deriving (Show, Eq)
  
data TCyp = TApplication TCyp TCyp | TConst String | TNRec String | TRec
	deriving (Show, Eq)
	
	
makeSteps rules (x:y:steps) aim 
    | y `elem` fst (unzip (applyall x rules)) = "" ++ (makeSteps rules (y:steps) aim)
    | otherwise = "Fehler :( : step " ++ printInfo x ++ " to " ++ printInfo  y
makeSteps rules [x] aim 
    | x == aim = "Erfolgreicher Beweis des aktuellen Goals"
    | x /= aim = "Hier fehlt noch was"
makeSteps _ _ _ = "Komischer Beweis :)"

applyall step rules = concatMap (\rule -> concat $ nub [apply step x y | x <- rule, y <- rule]) rules 


apply :: Cyp -> Cyp -> Cyp -> [(Cyp, [(Cyp, Cyp)])]
apply step@(Application cc c) rule@(Application ccr cr) to = 
    found ++ [(Application x c, y) | (x,y) <- apply cc (Application ccr cr) to] ++ [(Application cc x, y) | (x,y) <- apply c (Application ccr cr) to]
	    where
		    (fstt, sndt) = head $ apply cc ccr to
		    (fstc, sndc) = head $ (apply c cr to)
		    found
			    | (length (apply c cr to) > 0) && (length (apply cc ccr to) > 0) = [(edit to (sndt ++ sndc), (sndt ++ sndc))]
			    | otherwise = []
apply (Literal a) (Literal b) _
	| a == b = [(Literal a, [])]
	| otherwise = []
apply (Const a) (Const b) _
	| a == b = [(Const a, [])]
	| otherwise = []
apply x (Variable b) _ = [(Variable b, [(Variable b, x)])]
apply _ _ _ = []

edit :: Cyp -> [(Cyp, Cyp)] -> Cyp
edit (Application cypcurry cyp) x = Application (edit cypcurry x) (edit cyp x)
edit (Const a) _ = (Const a)
edit (Literal a) _ = (Literal a)
edit (Variable a) x = extract (lookup (Variable a) x)
	where
		extract (Just n) = n
		extract (Nothing) = (Variable a)
	
printCypEquoations [] = []
printCypEquoations (x:xs) = [map printInfo x] ++ (printCypEquoations xs)

printRunnable :: Cyp -> String
printRunnable (Application cypCurry cyp) = "(" ++ (printRunnable cypCurry) ++ " " ++ (printRunnable cyp) ++ ")"
printRunnable (Literal a) = translateLiteral a
printRunnable (Variable a) = a
printRunnable (Const a) = a

printInfo :: Cyp -> String
printInfo (Application cypCurry cyp) = "(" ++ (printInfo cypCurry) ++ " " ++ (printInfo cyp) ++ ")"
printInfo (Literal a) = translateLiteral a
printInfo (Variable a) = "?" ++ a
printInfo (Const a) = a

getGoals :: [TCyp] -> TCyp -> [(String, TCyp)]
getGoals xs goal = map (\x -> (getConstructorName x, getGoal x goal)) xs

getGoal :: TCyp -> TCyp -> TCyp
getGoal maybeGoal@(TApplication cypCurry cyp) goal
    | maybeGoal == goal = TRec
    | otherwise = TApplication (getGoal cypCurry goal) (getGoal cyp goal)
getGoal (TNRec a) goal = TNRec a
getGoal maybeGoal@(TConst a) goal
    | maybeGoal == goal = TRec
    | otherwise = TConst a

translateToTyp (Application cypcurry cyp) = TApplication (translateToTyp cypcurry) (translateToTyp cyp)
translateToTyp (Variable a) = TNRec a
translateToTyp (Const a) = TConst a

getConstructorName (TApplication (TConst a) cyp) = a
getConstructorName (TConst a) = a
getConstructorName (TApplication cypCurry cyp) = getConstructorName cypCurry

getLists :: Exp -> (ConstList, VariableList)
getLists (Var v) = ([], [translateQName v])
getLists (Con c) = ([translateQName c], [])
getLists (Lit l) = ([], [])
getLists (InfixApp e1 (QConOp i) e2) = (cs1 ++ cs2 ++ [translateQName i], vs1 ++ vs2)
    where
        (cs1,vs1) = getLists e1
        (cs2,vs2) = getLists e2
getLists (InfixApp e1 (QVarOp i) e2) = (cs1 ++ cs2 ++ [translateQName i], vs1 ++ vs2)
    where
        (cs1,vs1) = getLists e1
        (cs2,vs2) = getLists e2
getLists (App (Var e1) e2) = (cs2 ++ [translateQName e1], vs2)
    where (cs2,vs2) = getLists e2
getLists (App e1 e2) = (cs1 ++ cs2, vs1 ++ vs2)
    where
        (cs1,vs1) = getLists e1
        (cs2,vs2) = getLists e2
getLists (Paren e) = getLists e
getLists (List []) = (["[]"], [])
getLists (List (x:xs)) = (csh ++ cst ++ [":"], vsh ++ vst)
    where
        (csh,vsh) = getLists x
        (cst,vst) = getLists (List xs)

getConstList :: (ConstList, VariableList) -> ConstList
getConstList (cons ,_) = cons

getVariableList :: (ConstList, VariableList) -> VariableList
getVariableList (_, var) = var

translate :: Exp -> ConstList -> VariableList -> (String -> [String] -> Bool)-> Cyp
translate (Var v) cl vl f
    | elem (translateQName v) cl = Const (translateQName v)
    | f (translateQName v) vl = Variable (translateQName v)
translate (Con c) cl vl f = Const (translateQName c)
translate (Lit l) cl vl f = Literal l
translate (InfixApp e1 (QConOp i) e2) cl vl f = Application (Application (Const (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
translate (InfixApp e1 (QVarOp i) e2) cl vl f
    | elem (translateQName i) cl =  Application (Application (Const (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
    | f (translateQName i) vl =  Application (Application (Variable (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
translate (App (Var e1) e2) cl vl f = Application (Const (translateQName e1)) (translate e2 cl vl f)
translate (App e1 e2)  cl vl f = Application (translate e1 cl vl f) (translate e2 cl vl f)
translate (Paren e) cl vl f = translate e cl vl f
translate (List l) cl vl f
    | null(l) = Const ("[]")
    | otherwise = Application (Application (Const (":")) (translate (head l) cl vl f)) (translate (List (tail l)) cl vl f)

translateQName (Qual (ModuleName m) (Ident n)) = m ++ "." ++ n
translateQName (Qual (ModuleName m) (Symbol n)) = m ++ "." ++ n
translateQName (UnQual (Ident n)) = n
translateQName (UnQual (Symbol n)) = n
translateQName (Special UnitCon) = "()"
translateQName (Special ListCon) = "[]"
translateQName (Special FunCon) = "->"
translateQName (Special Cons) = ":"
translateQName _ = ""

translateLiteral (Char c) = [c]
translateLiteral (String s) = s
translateLiteral (Int c) = show c
translateLiteral (Frac c) = show c
translateLiteral (PrimInt c) = show c
translateLiteral (PrimWord c) = show c
translateLiteral (PrimFloat c) = show c
translateLiteral (PrimDouble c) = show c
translateLiteral (PrimChar c) = [c]
translateLiteral (PrimString c) = c

true :: a -> b -> Bool
true _ _ = True


mapFirstStep :: [[Cyp]] -> [[Cyp]] -> [String] -> [(String, TCyp)] -> ([[Cyp]], [Cyp], [(String, TCyp)], [Cyp])
mapFirstStep theses firststeps over goals = (map (\x -> map (\y -> createNewLemmata y (head over) x) (head theses)) (concat fmg), concat fmg, concat smg, concat tmg)
	where
		(fmg, smg, tmg) = unzip3 mapGoals
			where
				mapGoals = concatMap (\z -> map (\(y,x) -> goalLookup x z (head over) (y,x)) goals) (parseFirstStep (head $ head theses) (head $ head firststeps) (head over))
				
parseFirstStep :: Cyp -> Cyp -> String -> [Cyp]
parseFirstStep (Variable n) m over
	| over == n =  [m]
    | otherwise = []
parseFirstStep (Literal l) _ _ = []
parseFirstStep (Const c) _ _  = []
parseFirstStep (Application cypCurry cyp) (Application cypthesisCurry cypthesis) over = (parseFirstStep cypCurry cypthesisCurry over) ++ (parseFirstStep cyp cypthesis over)
parseFirstStep _ _ _ = []

goalLookup :: TCyp -> Cyp -> String -> (String, TCyp) -> ([Cyp], [(String, TCyp)], [Cyp])
goalLookup (TApplication tcypcurry tcyp) (Application cypcurry cyp) over x 
	| length  (sgl ++ scgl) == 0 = (fgl ++ fcgl, sgl ++ scgl, tgl ++ tcgl)
	| otherwise = ([], [], [])
	where
		(fgl, sgl, tgl) = goalLookup tcyp cyp over x
		(fcgl, scgl, tcgl) = goalLookup tcypcurry cypcurry over x
goalLookup (TConst a) (Const b) over x 
	| a == b = ([], [], [])
	| otherwise = ([], [x], [])
goalLookup (TNRec a) (Variable b) _ _ = ([], [], [Variable b])
goalLookup (TRec) b over x = ([b], [], [b])
goalLookup _ _ _  x = ([], [x], [])

createNewLemmata :: Cyp -> String -> Cyp -> Cyp
createNewLemmata (Application cypcurry cyp) over b =  Application (createNewLemmata cypcurry over b) (createNewLemmata cyp over b)
createNewLemmata (Variable a) over (Const b) 
	| over == a = Const b
	| otherwise = Variable a
createNewLemmata (Variable a) over (Variable b) 
	| over == a = Const b
	| otherwise = Variable a
createNewLemmata (Const a) over (Const b) 
	| over == a = Const b
	| otherwise = Const a
createNewLemmata (Const a) over (Variable b) 
	| over == a = Const b
	| otherwise = Const a
createNewLemmata (Literal a) _ _ = Literal a

varToConst xs =
  do 
    cyp <- xs
    return (concatMap (map transformVartoConst) cyp)

transformVartoConst :: Cyp -> Cyp
transformVartoConst (Variable v) = Const v
transformVartoConst (Const v) = Const v
transformVartoConst (Application cypCurry cyp) = Application (transformVartoConst cypCurry) (transformVartoConst cyp)
transformVartoConst (Literal a) = Literal a

getSteps rules steps aim =
    do 
        return (makeSteps rules steps aim)

getFirstStep thesis steps over goals =
	do
		return (mapFirstStep thesis steps over goals)

getDataType content expression = 
  do
    foo <- outterParse content expression
    return (getGoals (tail $ head $ (innerParseDataType foo)) (head $ head $ (innerParseDataType foo)))

getCyp content expression global = 
  do
    foo <- outterParse content expression
    return (innerParseCyp foo global)

getSym content expression = 
  do
    foo <- outterParse content expression
    return (innerParseSym foo)

getOver content expression global =
  do
    foo <- outterParse content expression
    return (concat $ map getVariableList (innerParseLists foo))

getFunc content expression sym = 
  do
    foo <- outterParse content expression
    return (parseFunc foo (innerParseLists foo) (nub $ globalConstList (innerParseLists foo) sym), nub $ globalConstList (innerParseLists foo) sym)
		
globalConstList (x:xs) ys = getConstList x ++ (globalConstList xs ys)
globalConstList [] ((Const y):ys) = y : (globalConstList [] ys)
globalConstList [] [] = []

parseFunc r l g = zipWith (\a b -> [a, b]) (innerParseFunc r g l head) (innerParseFunc r g l last)

innerParseFunc [] _ _ _ = []
innerParseFunc (x:xs) g (v:vs) f = (parseDef (f (splitStringAt "=" x [])) g (getVariableList v)):(innerParseFunc xs g vs f)
  where
    parseDef x g v = translate (transform $ parseExp $ x) g v elem

innerParseLists [] = []
innerParseLists (x:xs) = (parseLists $ head (splitStringAt "=" x [])):(innerParseLists xs)
		
parseLists x = getLists $ transform $ parseExp $ x
		
innerParseCyp [] _ = []
innerParseCyp (x:xs) global = parseCyp (splitStringAt "=" x []) global:(innerParseCyp xs global)

parseCyp [] _ = []
parseCyp (x:xs) global = translate (transform $ parseExp x) global [] true : (parseCyp xs global)

innerParseSym [] = []
innerParseSym (x:xs) = parseSym (splitStringAt "=" x []):(innerParseSym xs)

parseSym [] = []
parseSym (x:xs) = (translate (transform $ parseExp x) [] [] true)  : (parseSym xs)

innerParseDataType [] = []
innerParseDataType (x:xs) = parseDataType (splitStringAt "=|" x []):(innerParseDataType xs)

parseDataType [] = []
parseDataType (x:xs) = (translateToTyp (translate (transform $ parseExp x) [] [] true))  : (parseDataType xs)

transform (ParseOk a) = a

outterParse content expression = 
  do
    return $ trim $ deleteAll splitH deleteH
      where
      	deleteH = (\x -> ( x == "") || ( x == expression))
      	splitH = splitStringAt "#" (replace expression "" $ concat matchReg) []
      	  where
      	    matchReg = extract (matchRegex regex (deleteAll content isControl))
      	      where
            		regex = mkRegex (expression ++ "(.*)" ++ expression)
            		extract (Just x) = x
    	
deleteAll :: Eq a => [a] -> (a->Bool) -> [a]
deleteAll [] _ = []
deleteAll (x:xs) a 
	| a x = deleteAll xs a
	| otherwise = x : (deleteAll xs a)
									 
splitStringAt :: Eq a => [a] -> [a] -> [a] -> [[a]]
splitStringAt a [] h 
	| h == [] = []
	| otherwise = h : []
splitStringAt a (x:xs) h 
	| x `elem` a = h : splitStringAt a xs []
	| otherwise = splitStringAt a xs (h++[x])
												 
trim (x:xs) = trimh (trimh x):trim xs
  where
    trimh = reverse . dropWhile isSpace
trim [] = []

replace _ _ [] = []
replace old new (x:xs) 
	| isPrefixOf old (x:xs) = new ++ drop (length old) (x:xs)
	| otherwise = x : replace old new xs
