# Práctica 02: Sintaxis y Semántica de la Lógica Proposicional

## Integrantes del equipo
Rodrigo Emanuel Villegas del Angel 
Correo: ryureva3@ciencias.unam.mx
---

## Explicación de las funciones implementadas

### 1. `show` (Instancia de `Show`)
Esta función convierte una fórmula de tipo `Prop` en una cadena de texto legible. Por ejemplo, la fórmula `Conj (Var "p") (Var "q")` se convierte en `"(p /\ q)"`. Se implementó usando recursión para recorrer la fórmula y concatenar los símbolos correctos.

---

### 2. `conjPotencia`
Esta función genera todos los subconjuntos posibles de una lista. Por ejemplo, para la lista `[1, 2]`, devuelve `[[], [1], [2], [1, 2]]`. Se implementó usando recursión: para cada elemento, se generan los subconjuntos que lo incluyen y los que no.

---

### 3. `vars`
Esta función devuelve una lista de todas las variables que aparecen en una fórmula. Por ejemplo, para la fórmula `Conj (Var "p") (Var "q")`, devuelve `["p", "q"]`. Se implementó recorriendo la fórmula y recolectando las variables, usando `nub` para eliminar duplicados.

---

### 4. `interpretacion`
Esta función evalúa una fórmula en un estado dado (un estado es una lista de variables que son verdaderas). Por ejemplo, para la fórmula `Conj (Var "p") (Var "q")` y el estado `["p"]`, devuelve `False` porque `q` no está en el estado. Se implementó usando recursión para evaluar cada parte de la fórmula según el estado.

---

### 5. `modelos`
Esta función devuelve todos los estados que hacen que la fórmula sea verdadera. Por ejemplo, para la fórmula `Var "p"`, devuelve `[["p"]]`. Se implementó generando todos los subconjuntos de variables (`conjPotencia`) y filtrando los que hacen verdadera la fórmula.

---

### 6. `tautologia`
Esta función verifica si una fórmula es una tautología (siempre es verdadera, sin importar el estado). Por ejemplo, `Disy (Var "p") (Neg (Var "p"))` es una tautología. Se implementó verificando si todos los estados hacen verdadera la fórmula.

---

### 7. `contradiccion`
Esta función verifica si una fórmula es una contradicción (siempre es falsa, sin importar el estado). Por ejemplo, `Conj (Var "p") (Neg (Var "p"))` es una contradicción. Se implementó verificando si ningún estado hace verdadera la fórmula.

---

### 8. `esSatisfacible`
Esta función verifica si una fórmula es satisfacible (existe al menos un estado que la hace verdadera). Por ejemplo, `Var "p"` es satisfacible. Se implementó verificando si hay al menos un modelo para la fórmula.

---

### 9. `deMorgan`
Esta función aplica las leyes de De Morgan para simplificar fórmulas. Por ejemplo, `~(p /\ q)` se convierte en `~p \/ ~q`. Se implementó recorriendo la fórmula y aplicando las leyes de De Morgan donde sea necesario.

---

### 10. `elimImplicacion`
Esta función elimina las implicaciones (`->`) de una fórmula, reemplazándolas por disyunciones y negaciones. Por ejemplo, `Impl (Var "p") (Var "q")` se convierte en `Disy (Neg (Var "p")) (Var "q")`. Se implementó usando la equivalencia `p -> q` ≡ `~p \/ q`.

---

### 11. `elimEquivalencias`
Esta función elimina las equivalencias (`<->`) de una fórmula, reemplazándolas por conjunciones de implicaciones. Por ejemplo, `Equiv (Var "p") (Var "q")` se convierte en `Conj (Impl (Var "p") (Var "q")) (Impl (Var "q") (Var "p"))`. Se implementó usando la equivalencia `p <-> q` ≡ `(p -> q) /\ (q -> p)`.

---

## Cómo ejecutar las pruebas
Para ejecutar las pruebas, usa el siguiente comando en la terminal:

```bash
runhaskell Test.hs