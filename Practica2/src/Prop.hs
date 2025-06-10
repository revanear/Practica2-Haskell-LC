module Prop where
-- Profesor: Manuel Soto Romero
-- Ayudante: Diego Méndez Medina
-- Ayudante: José Alejandro Pérez Marquez
-- Laboratorio: Erick Daniel Arroyo Martínez
-- Laboratorio: Erik Rangel Limón
import Data.List (nub)

-- ------------------------------------------------------------------------------
-- Definicion de los tipos de datos siguientes:
-- Prop para representar las fórmulas proporsicionales usando los
-- constructores T, F, Var, Neg, Conj, Disy, Impl y Equiv para formulas atomicas,
-- negaciones, conjunciones, implicaciones y equivalencias respectivamente.
-- ------------------------------------------------------------------------------

data Prop = T | F | Var String
          | Neg Prop
          | Conj Prop Prop | Disy Prop Prop 
          | Impl Prop Prop | Equiv Prop Prop deriving Eq

type Estado = [String]

-- ------------------------------------------------------------------------------
-- Ejercicio 1.
-- Definir un ejemplar de la clase Show para el tipo de dato Prop que muestre una
-- cadena que represente las formulas proposicionales en notacion infija.
-- ------------------------------------------------------------------------------

instance Show Prop where
    --show :: Prop -> String
    show T = "T"
    show F = "F"
    show (Var s) = s
    show (Neg p) = "¬" ++ show p
    show (Conj a b) = "(" ++ show a ++ " /\\ " ++ show b ++ ")"
    show (Disy a b) = "(" ++ show a ++ " \\/ " ++ show b ++ ")"
    show (Impl a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
    show (Equiv a b) = "(" ++ show a ++ " <-> " ++ show b ++ ")"
    
    
-- ------------------------------------------------------------------------------
-- Ejercicio 2
-- Definir la funcion conjPotencia, tal que la aplicación de la funcion es la
-- lista de todos los subconjuntos de x.
-- ------------------------------------------------------------------------------
conjPotencia :: [a] -> [[a]]
conjPotencia [] = [[]]
conjPotencia (x:xs) = let ps = conjPotencia xs in ps ++ map (x:) ps

-- ------------------------------------------------------------------------------
-- Ejercicio 3.
-- Definir la función vars::Prop -> [String] que devuelve el conjunto de variables
-- proposicionales de una fórmula.
-- ------------------------------------------------------------------------------

vars :: Prop -> [String]
vars T = []
vars F = []
vars (Var s) = [s]
vars (Neg p) = vars p
vars (Conj a b) = nub (vars a ++ vars b)
vars (Disy a b) = nub (vars a ++ vars b)
vars (Impl a b) = nub (vars a ++ vars b)
vars (Equiv a b) = nub (vars a ++ vars b)

-- ------------------------------------------------------------------------------
-- Ejercicio 4.
-- Definir la función interpreta que dada una formula proposicional y un estado
-- regrese la interpretación obtenida de la fórmula en dicho estado.
-- ------------------------------------------------------------------------------
    
interpretacion :: Prop -> Estado -> Bool
interpretacion T _ = True
interpretacion F _ = False
interpretacion (Var s) e = s `elem` e
interpretacion (Neg p) e = not (interpretacion p e)
interpretacion (Conj a b) e = interpretacion a e && interpretacion b e
interpretacion (Disy a b) e = interpretacion a e || interpretacion b e
interpretacion (Impl a b) e = not (interpretacion a e) || interpretacion b e
interpretacion (Equiv a b) e = interpretacion a e == interpretacion b e

-- ------------------------------------------------------------------------------
-- Ejercicio 5.
-- Definir la funcion modelos :: Prop -> [Estado] que dada una fórmula devuelve
-- una lista de estados que satisfacen a dicha fórmula.
-- ------------------------------------------------------------------------------
modelos :: Prop -> [Estado]
modelos prop = filter (interpretacion prop) (conjPotencia (vars prop))

-- ------------------------------------------------------------------------------
-- Ejercicio 6.
-- Definir una función que dada una fórmula proposicional, indique si es una 
-- tautologia.
-- Firma de la funcion: tautologia:: Prop -> Bool
-- ------------------------------------------------------------------------------

tautologia :: Prop -> Bool
tautologia prop = all (interpretacion prop) (conjPotencia (vars prop))

-- ------------------------------------------------------------------------------
-- Ejercicio 7.
-- Definir una funcion que dada una fórmula proposicional, indique si es una
-- contradicción.
-- firma de la funcion: contradiccion :: Prop -> Bool
-- ------------------------------------------------------------------------------
contradiccion :: Prop -> Bool
contradiccion = null . modelos

-- ------------------------------------------------------------------------------
-- Ejercicio 8.
-- Definir una función que dada una fórmula proposicional phi, verifique si es 
-- satisfacible.
-- ------------------------------------------------------------------------------
esSatisfacible :: Prop -> Bool
esSatisfacible = not . contradiccion

-- ------------------------------------------------------------------------------
-- Ejercicio 9.

-- Definir una función que elimine dobles negaciones y aplique las
-- leyes de DeMorgan dada una fórmula proposicional phi.
-- ------------------------------------------------------------------------------
deMorgan :: Prop -> Prop
deMorgan (Neg (Neg p)) = deMorgan p
deMorgan (Neg (Conj a b)) = Disy (deMorgan (Neg a)) (deMorgan (Neg b))
deMorgan (Neg (Disy a b)) = Conj (deMorgan (Neg a)) (deMorgan (Neg b))
deMorgan (Neg p) = Neg (deMorgan p)
deMorgan (Conj a b) = Conj (deMorgan a) (deMorgan b)
deMorgan (Disy a b) = Disy (deMorgan a) (deMorgan b)
deMorgan (Impl a b) = Impl (deMorgan a) (deMorgan b)
deMorgan (Equiv a b) = Equiv (deMorgan a) (deMorgan b)
deMorgan x = x

-- ------------------------------------------------------------------------------
-- Ejercicio 10.
-- Definir una función que elimine las implicaciones lógicas de una proposición
-- ------------------------------------------------------------------------------
elimImplicacion :: Prop -> Prop
elimImplicacion (Impl a b) = Disy (Neg (elimImplicacion a)) (elimImplicacion b)
elimImplicacion (Neg p) = Neg (elimImplicacion p)
elimImplicacion (Conj a b) = Conj (elimImplicacion a) (elimImplicacion b)
elimImplicacion (Disy a b) = Disy (elimImplicacion a) (elimImplicacion b)
elimImplicacion (Equiv a b) = Equiv (elimImplicacion a) (elimImplicacion b)
elimImplicacion x = x

-- ------------------------------------------------------------------------------
-- Ejercicio 11.
-- Definir una funcion que elimine las equivalencias lógicas de una proposición.
-- ------------------------------------------------------------------------------
elimEquivalencias :: Prop -> Prop
elimEquivalencias (Equiv a b) = Conj (Impl a' b') (Impl b' a')
    where a' = elimEquivalencias a
          b' = elimEquivalencias b
elimEquivalencias (Impl a b) = Impl (elimEquivalencias a) (elimEquivalencias b)
elimEquivalencias (Neg p) = Neg (elimEquivalencias p)
elimEquivalencias (Conj a b) = Conj (elimEquivalencias a) (elimEquivalencias b)
elimEquivalencias (Disy a b) = Disy (elimEquivalencias a) (elimEquivalencias b)
elimEquivalencias x = x

-- ------------------------------------------------------------------------------
-- Número de pruebas a hacer.
-- Puedes cambiar este valor siempre y cuando éste sea mayor o igual a 100.
-- ------------------------------------------------------------------------------
pruebas :: Int
pruebas = 1000
