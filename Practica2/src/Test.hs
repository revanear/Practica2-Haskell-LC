module Test where

import Prop

import Test.QuickCheck

import Control.Arrow (first)
import Data.Bool (bool)
import Data.Char (isSpace, isAlpha)
import Data.List (nub, (\\))

newtype Prs a = Prs {prs :: String -> [(a,String)]}

instance Functor Prs where
  fmap = (Prs .) . (. prs) . (.) . fmap . first

instance Applicative Prs where
  pure = Prs . ((: []) .) . (,)
  (<*>) = (Prs .) . ((concat .) .) . (. fmap . uncurry . (prs .) . flip fmap) . flip (.) . prs

instance Monad Prs where
  (>>=) = (Prs .) . ((concat .) .) . (. fmap . uncurry . (prs .)) . flip (.) . prs

atMost1 [] = []
atMost1 (x:_) = [x]

(+++) :: Prs a -> Prs a -> Prs a
(+++) = (Prs .) . ((atMost1 .) .) . (. prs) . (<*>) . ((++) .) . prs

item :: Prs Char
item = Prs (\str -> case str of
                    [] -> []
                    (x:xs) -> [(x,xs)])

if' :: Bool -> a -> a -> a
if' = (. flip bool) . flip flip

sat :: (Char -> Bool) -> Prs Char
sat = (item >>=) . (<*> return) . (flip flip (Prs $ const []) .) . (if' .)

char :: Char -> Prs Char
char = sat . (==)

many :: Prs a -> Prs [a]
many = (+++ return []) . many1

many1 :: Prs a -> Prs [a]
many1 = (<*>) . ((:) <$>) <*> many

space :: Prs String
space = many $ sat isSpace

str :: String -> Prs String
str [] = return ""
str (x:xs) = char x >> str xs >> return (x:xs)

tok :: Prs a -> Prs a
tok = (space >>) . (>>= (space >>) . return)

symb :: String -> Prs String
symb = tok . str

symprs :: String -> a -> Prs a
symprs xs a = symb xs >> return a

prop :: Prs Prop
prop = var +++ symprs "T" T +++ symprs "F" F +++ neg +++ precon

var :: Prs Prop
var = fmap Var $ tok $ many1 $ sat isAlpha

neg :: Prs Prop
neg = symb "¬" >> (Neg <$> prop)

precon :: Prs Prop
precon = symb "(" >> con >>= (symb ")" >>) . return

con :: Prs Prop
con = conj +++ disy +++ impl +++ equiv

conj :: Prs Prop
conj = prop >>= (symb "/\\" >>) . (prop >>=) . (return .) . Conj

disy :: Prs Prop
disy = prop >>= (symb "\\/" >>) . (prop >>=) . (return .) . Disy

impl :: Prs Prop
impl = prop >>= (symb "->" >>) . (prop >>=) . (return .) . Impl

equiv :: Prs Prop
equiv = prop >>= (symb "<->" >>) . (prop >>=) . (return .) . Equiv

varProp :: Int -> Gen (Prop, [String])
varProp n = do
  lv <- chooseInt (0,n)
  genProp [] lv
  where
    genProp xs lv | lv <= 0 = do
                      x <- chooseEnum ('a','z')
                      return (Var [x], nub ([x]:xs))
                  | otherwise = do
                      b <- arbitrary
                      if b then do
                        (prop, ys) <- genProp xs (lv-1)
                        return (Neg prop, ys)
                        else do
                        b' <- arbitrary
                        n <- chooseInt (0,lv-1)
                        (p, ps) <- genProp xs (lv-1)
                        (q, qs) <- genProp xs n
                        con <- elements [Disy,Conj,Impl,Equiv]
                        return $ if b' then
                                   (con p q, nub $ ps ++ qs)
                                 else
                                   (con q p, nub $ ps ++ qs)

prop_showOk :: Property
prop_showOk = forAll (fmap fst $ varProp 15) (\p -> (p ==) $ fst $ head $ prs prop $ show p)

check_show :: Int -> IO ()
check_show n = quickCheck $ withMaxSuccess n prop_showOk

differents :: (Arbitrary a, Eq a) => Int -> Gen [a]
differents n | n <= 0 = return []
             | otherwise = do
                 xs <- differents (n-1)
                 x <- arbitrary `suchThat` (not . (`elem` xs))
                 return (x:xs)

diffInts :: Int -> Gen [Int]
diffInts s = do
  n <- chooseInt (0,s)
  differents n

prop_conjOk :: Property
prop_conjOk = forAll (diffInts 10) fun
  where
    subset xs ys = all (`elem` ys) xs
    fun xs = let n = length xs
                 pot = conjPotencia xs
                 twoN = length pot
             in pot == nub pot && 2 ^ n == twoN && all (`subset` xs) pot

check_conjPotencia :: Int -> IO ()
check_conjPotencia n = quickCheck $ withMaxSuccess n prop_conjOk

prop_varsOk :: Property
prop_varsOk = forAll (varProp 30) (\(p,vs) -> vars p `equiv` vs)
  where
    equiv xs ys = all (`elem` xs) ys && all (`elem` ys) xs

check_vars :: Int -> IO ()
check_vars n = quickCheck $ withMaxSuccess n prop_varsOk

ranInterp :: Gen (Prop, [String])
ranInterp = do
  (prop, xs) <- varProp 30
  xs' <- shuffle xs
  xs'' <- sublistOf xs'
  return (prop, xs'')

prop_interpOk :: Property
prop_interpOk = forAll ranInterp $ uncurry fun
  where
    fun p@(Var x) st = if interpretacion p st then
                         elem x st
                       else
                         not (elem x st)
    fun p@(Neg q) st = if interpretacion p st then
                         not $ interpretacion q st
                       else
                         interpretacion q st
    fun p@(Disy q s) st = if interpretacion p st then
                            interpretacion q st || interpretacion s st
                          else
                            not (interpretacion q st || interpretacion s st)
    fun p@(Conj q s) st = if interpretacion p st then 
                            interpretacion q st && interpretacion s st
                          else
                            not (interpretacion q st && interpretacion s st)
    fun p@(Impl q s) st = if interpretacion p st then
                            not (interpretacion q st) || interpretacion s st
                          else
                            not (not (interpretacion q st) || interpretacion s st)
    fun p@(Equiv q s) st = if interpretacion p st then
                            (not (interpretacion q st) || interpretacion s st) && (not (interpretacion s st) || interpretacion q st)
                          else
                            not ((not (interpretacion q st) || interpretacion s st) && (not (interpretacion s st) || interpretacion q st))

check_interpretacion :: Int -> IO ()
check_interpretacion n = quickCheck $ withMaxSuccess n prop_interpOk

-- | Depende de interpretacion
prop_modelosOk :: Property
prop_modelosOk = forAll (fmap fst $ varProp 6) (\p -> all (interpretacion p) $ modelos p)

-- | Depende de interpretacion y conjPotencia
prop_modelosNotOk :: Property
prop_modelosNotOk = forAll (fmap fst $ varProp 6) (\p -> all (not . interpretacion p) $ conjPotencia (nub $ vars $ p) \\ modelos p)

check_modelos :: Int -> IO ()
check_modelos n = do
  quickCheck $ withMaxSuccess n prop_modelosOk
  quickCheck $ withMaxSuccess n prop_modelosNotOk

tauts :: Gen Prop
tauts = fmap genTaut $ chooseInt (1,7)
  where
    genTaut n = suc $ foldr1 Conj $ map (Var . (:[])) $ take n ['a'..]
    last (Neg prop) = True
    last (Conj (Neg _) prop) = last prop
    last _ = False
    next (Neg p) = p
    next (Var x) = Neg (Var x)
    next (Conj (Var x) ps) = Conj (Neg (Var x)) ps
    next (Conj (Neg p) ps) = Conj p $ next ps
    suc prop | last prop = prop
             | otherwise = Disy prop $ suc (next prop)

contrs :: Gen Prop
contrs = fmap Neg tauts

prop_tautOk :: Property
prop_tautOk = forAll tauts tautologia

prop_tautNotOk :: Property
prop_tautNotOk = forAll contrs (not . tautologia)

check_tautologia :: Int -> IO ()
check_tautologia n = do
  quickCheck $ withMaxSuccess n prop_tautOk
  quickCheck $ withMaxSuccess n prop_tautNotOk

prop_contrOk :: Property
prop_contrOk = forAll contrs contradiccion

prop_contrNotOk :: Property
prop_contrNotOk = forAll tauts (not . contradiccion)

check_contradiccion :: Int -> IO ()
check_contradiccion n = do
  quickCheck $ withMaxSuccess n prop_contrOk
  quickCheck $ withMaxSuccess n prop_contrNotOk

sats :: Gen Prop
sats = tauts >>= toSat
  where
    ln (Disy p q) = 1 + ln q
    ln _ = 1
    elim (Disy p q) n | n <= 0 = q
                      | otherwise = Disy p $ elim q (n-1)
    elim p _ = p
    toSat p = chooseInt (0, ln p - 1) >>= aux p
    aux p n | n <= 0 = return p
            | otherwise = do
                x <- chooseInt (0, ln p - 1)
                aux (elim p x) (n - 1)

prop_satOk :: Property
prop_satOk = forAll sats esSatisfacible

prop_satNotOk :: Property
prop_satNotOk = forAll contrs (not . esSatisfacible)

check_esSatisfacible :: Int -> IO ()
check_esSatisfacible n = do
  quickCheck $ withMaxSuccess n prop_satOk
  quickCheck $ withMaxSuccess n prop_satNotOk

prop_deMorganTopo :: Property
prop_deMorganTopo = forAll (fmap fst $ varProp 30) (topo . deMorgan)
  where
    topo T = True
    topo F = True
    topo (Var _) = True
    topo (Neg (Neg _)) = False
    topo (Neg (Conj _ _)) = False
    topo (Neg (Disy _ _)) = False
    topo (Neg p) = topo p
    topo (Conj p q) = topo p && topo q
    topo (Disy p q) = topo p && topo q
    topo (Impl p q) = topo p && topo q
    topo (Equiv p q) = topo p && topo q

eqFun :: (Prop -> Prop) -> Property
eqFun dm = forAll (fmap fst $ varProp 7) fun
  where
    fun p = all (\xs -> interpretacion p xs == interpretacion (dm p) xs) $ conjPotencia $ nub $ vars p

prop_deMorganEquiv :: Property
prop_deMorganEquiv = eqFun deMorgan

check_deMorgan :: Int -> IO ()
check_deMorgan n = do
  quickCheck $ withMaxSuccess n prop_deMorganTopo
  quickCheck $ withMaxSuccess n prop_deMorganEquiv

prop_implTopo :: Property
prop_implTopo = forAll (fmap fst $ varProp 30) (topo . elimImplicacion)
  where
    topo T = True
    topo F = True
    topo (Var _) = True
    topo (Neg p) = topo p
    topo (Conj p q) = topo p && topo q
    topo (Disy p q) = topo p && topo q
    topo (Impl _ _) = False
    topo (Equiv p q) = topo p && topo q

prop_implEquiv :: Property
prop_implEquiv = eqFun elimImplicacion

check_elimImplicacion :: Int -> IO ()
check_elimImplicacion n = do
  quickCheck $ withMaxSuccess n prop_implTopo
  quickCheck $ withMaxSuccess n prop_implEquiv

prop_equivTopo :: Property
prop_equivTopo = forAll (fmap fst $ varProp 30) (topo . elimEquivalencias)
  where
    topo T = True
    topo F = True
    topo (Var _) = True
    topo (Neg p) = topo p
    topo (Conj p q) = topo p && topo q
    topo (Disy p q) = topo p && topo q
    topo (Impl p q) = topo p && topo q
    topo (Equiv _ _) = False

prop_equivEquiv :: Property
prop_equivEquiv = eqFun elimEquivalencias

check_elimEquivalencias :: Int -> IO ()
check_elimEquivalencias n = do
  quickCheck $ withMaxSuccess n prop_equivTopo
  quickCheck $ withMaxSuccess n prop_equivEquiv

main :: IO ()
main = do
  let n = pruebas
  putStrLn "Pruebas show:"
  show1 <- quickCheckResult $ withMaxSuccess n prop_showOk
  putStrLn "Pruebas conjPotencia:"
  conj1 <- quickCheckResult $ withMaxSuccess n prop_conjOk
  putStrLn "Pruebas vars:"
  vars1 <- quickCheckResult $ withMaxSuccess n prop_varsOk
  putStrLn "Pruebas interpretacion:"
  interp1 <- quickCheckResult $ withMaxSuccess n prop_interpOk
  putStrLn "Pruebas modelos:"
  model1 <- quickCheckResult $ withMaxSuccess n prop_modelosOk
  model2 <- quickCheckResult $ withMaxSuccess n prop_modelosNotOk
  putStrLn "Pruebas tautologia:"
  taut1 <- quickCheckResult $ withMaxSuccess n prop_tautOk
  taut2 <- quickCheckResult $ withMaxSuccess n prop_tautNotOk
  putStrLn "Pruebas contradiccion:"
  contr1 <- quickCheckResult $ withMaxSuccess n prop_contrOk
  contr2 <- quickCheckResult $ withMaxSuccess n prop_contrNotOk
  putStrLn "Pruebas esSatisfacible:"
  sat1 <- quickCheckResult $ withMaxSuccess n prop_satOk
  sat2 <- quickCheckResult $ withMaxSuccess n prop_satNotOk
  putStrLn "Pruebas deMorgan:"
  dem1 <- quickCheckResult $ withMaxSuccess n prop_deMorganTopo
  dem2 <- quickCheckResult $ withMaxSuccess n prop_deMorganEquiv
  putStrLn "Pruebas elimImplicacion:"
  imp1 <- quickCheckResult $ withMaxSuccess n prop_implTopo
  imp2 <- quickCheckResult $ withMaxSuccess n prop_implEquiv
  putStrLn "Pruebas elimEquivalencias:"
  eq1 <- quickCheckResult $ withMaxSuccess n prop_equivTopo
  eq2 <- quickCheckResult $ withMaxSuccess n prop_equivEquiv
  let ok = length $ filter isSuccess [show1, conj1, vars1, interp1, model1, model2, taut1, taut2, contr1, contr2, sat1, sat2, dem1, dem2, imp1, imp2, eq1, eq2]
  putStrLn $ "Pruebas exitosas: " ++ show ok ++ "/18"
  let sh = if isSuccess show1 then 1 else 0
  let conj = if isSuccess conj1 then 1 else 0
  let vars = if isSuccess vars1 then 1 else 0
  let interp = if isSuccess interp1 then 1 else 0
  let model = fromIntegral $ length $ filter isSuccess [model1, model2]
  let taut = fromIntegral $ length $ filter isSuccess [taut1, taut2]
  let contr = fromIntegral $ length $ filter isSuccess [contr1, contr2]
  let sat = fromIntegral $ length $ filter isSuccess [sat1, sat2]
  let dem = fromIntegral $ length $ filter isSuccess [dem1, dem2]
  let imp = fromIntegral $ length $ filter isSuccess [imp1, imp2]
  let eq = fromIntegral $ length $ filter isSuccess [eq1, eq2]
  let calif = (sh + conj + vars + interp + model/2 + taut/2 + contr/2 + sat/2 + dem/2 + imp/2 + eq/2) / 11 * 10
  putStrLn $ "Calificación tentativa: " ++ show calif
