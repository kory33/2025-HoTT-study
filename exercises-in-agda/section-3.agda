module _ where
  -- Hack: Writing a public open import here in a top-level anonymous module
  --       allows all section modules (e.g. section-5, section-6, ...) following this module (section-3) to use 
  --       all transitively past section modules (e.g. section-2) without needing to additionally import them. 
  open import section-2 public

  data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

  Nat-ind : {P : Nat → Set} → P zero → ((n : Nat) → P n → P (succ n)) → (n : Nat) → P n
  Nat-ind {P} p0 ps = go where
    go : (n : Nat) → P n
    go zero = p0
    go (succ n) = ps n (go n)

  module NatBasic where
    one : Nat
    one = succ zero

    predOrZero : Nat → Nat
    predOrZero zero = zero
    predOrZero (succ n) = n

    add : Nat → Nat → Nat
    add m zero = m
    add m (succ n) = succ (add m n)

    -- exercise 3.1.a
    mul : Nat → Nat → Nat
    mul m zero = zero
    mul m (succ n) = add m (mul m n)

    -- exercise 3.1.b
    pow : Nat → Nat → Nat
    pow m zero = one
    pow m (succ n) = mul m (pow m n)

    module Symbolic where
      _+_ : Nat → Nat → Nat
      _+_ = add
      infixl 35 _+_

      _*_ : Nat → Nat → Nat
      _*_ = mul
      infixl 40 _*_

      _**_ : Nat → Nat → Nat
      _**_ = pow
      infixl 45 _**_
    open Symbolic

    module SymbolicQuantified where
      _+ℕ_ : Nat → Nat → Nat
      _+ℕ_ = add
      infixl 35 _+ℕ_

      _*ℕ_ : Nat → Nat → Nat
      _*ℕ_ = mul
      infixl 40 _*ℕ_

      _**ℕ_ : Nat → Nat → Nat
      _**ℕ_ = pow
      infixl 45 _**ℕ_

    -- exercise 3.2
    min : Nat → Nat → Nat
    min zero m = zero
    min (succ n) zero = zero
    min (succ n) (succ m) = succ (min n m)

    -- exercise 3.2
    max : Nat → Nat → Nat
    max zero m = m
    max (succ n) zero = succ n
    max (succ n) (succ m) = succ (max n m)

    -- exercise 3.3.a
    triangular : Nat → Nat
    triangular zero = zero
    triangular (succ n) = (succ n) + (triangular n)

    -- exercise 3.3.b
    factorial : Nat → Nat
    factorial zero = one
    factorial (succ n) = (succ n) * (factorial n)

    -- exercise 3.4
    binomial : Nat → Nat → Nat
    binomial zero zero = one
    binomial zero (succ _) = zero
    binomial (succ n) zero = one
    binomial (succ n) (succ m) = (binomial n m) + (binomial n (succ m))

    -- exercise 3.5
    fibonacci : Nat → Nat
    fibonacci n = grid n zero where
      grid : Nat → Nat → Nat
      grid zero zero = one
      grid zero (succ _) = zero
      grid (succ n) zero = (grid n zero) + (grid n one)
      grid (succ n) (succ _) = grid n zero

    -- exercise 3.6
    divBy2 : Nat → Nat
    divBy2 zero = zero
    divBy2 (succ zero) = zero
    divBy2 (succ (succ n)) = succ (divBy2 n)

    -- exercise 3.6
    divBy2' : Nat → Nat
    divBy2' n =
      Nat-ind zero (λ m _ →
        Nat-ind zero (λ k prevprev →
          succ prevprev
        ) m
      ) n
 