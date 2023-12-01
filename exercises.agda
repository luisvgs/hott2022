open import Agda.Builtin.Equality

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
zero + m = m
suc m + n = suc (m + n)

_*_ : Nat → Nat → Nat
zero * n = zero
suc m * n = n + (m * n)


data Bool : Set where
  true : Bool
  false : Bool

-- Exercise #1
-- In the lectures we defined && (logical and) on Bool by pattern matching on the leftmost argument only.
-- Define the same operation but this time by pattern matching (case splitting) on both arguments.
_&&_ : Bool -> Bool -> Bool
true && true = true
false && true = false
false && false = true
true && false = false


-- Exercise #3
-- Define the exponential and factorial functions on natural numbers.
_^_ : Nat -> Nat -> Nat
m ^ zero = suc (zero) -- 1
m ^ suc n =  (n ^ m) * n

-- Exercise 5
-- Use pattern matching on lists to define map.
-- This function should behave as follows:
-- map f [x₁ , x₂ , ... , xₙ] = [f x₁ , f x₂ , ... , f xₙ].
-- That is, map f xs applies the given function f to every element of the list xs and returns the resulting list.
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A
infixr 18 _::_

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (h :: t) = f h :: map f t

map-example : map (_+ 3) (1 :: 2 :: 3 :: []) ≡ 4 :: 5 :: 6 :: []
map-example = refl

-- Exercise 6 (★★)
-- Define a function filter that takes predicate p : X → Bool and a list xs that returns the list of elements of xs for which p is true.
filter : {X : Set} (p : X -> Bool) -> List X -> List X
filter p [] = []
filter p (x :: xs ) with p x
... | true = x :: filter p xs
... | false = filter p xs
