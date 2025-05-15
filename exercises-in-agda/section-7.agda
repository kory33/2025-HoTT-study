module _ where
  open import section-6 public

  Divides : Nat → Nat → Set
  Divides m n = Σ Nat (λ k → NatBasic.mul m k ≡ n)

  module DivisibilityBasic where
    module Symbolic where
      _∣_ : Nat → Nat → Set
      m ∣ n = Divides m n
      infix 30 _∣_
    open Symbolic

    open NatCommSemiring
    open NatBasic.Symbolic
    open ≡-Reasoning

    divides-refl : (m : Nat) → m ∣ m
    divides-refl m = pair one (mul-runit m)

    -- 7.1.4
    one-divides-any : (m : Nat) → one ∣ m
    one-divides-any m = pair m (mul-lunit m)

    -- 7.1.5
    divides-both-then-divides-sum : (d x y : Nat) → d ∣ x → d ∣ y → d ∣ (x + y)
    divides-both-then-divides-sum d x y (pair k p) (pair l q) =
      pair (k + l) (begin
        d * (k + l)     ≡⟨ mul-ldistr d k l ⟩
        d * k + d * l   ≡⟨ ap (λ e → e + d * l) p ⟩
        x + d * l       ≡⟨ ap (λ e → x + e) q ⟩
        x + y           ∎
      )
    
    -- TODO: exercise 7.1

  CongrMod : (x y k : Nat) → Set
  CongrMod x y k = Divides k (Nat-dist x y)

  module CongrModBasic where
    module Symbolic where
      _≡_mod_ : Nat → Nat → Nat → Set
      x ≡ y mod k = CongrMod x y k

      infix 30 _≡_mod_
    open Symbolic

    open ≡-Reasoning
    open NatCommSemiring
    open DivisibilityBasic.Symbolic

    -- 7.2.3
    congr-to-zero-mod-self : (x : Nat) → x ≡ zero mod x
    congr-to-zero-mod-self x =
      tr (λ e → x ∣ e) (inverse (Nat-dist.dist-to-zero x)) (DivisibilityBasic.divides-refl x)
    
    -- TODO: 7.2.4

  classical-Fin : (k : Nat) → Set
  classical-Fin k = Σ Nat (λ x → Lt-Nat x k)

  Fin : (k : Nat) → Set
  Fin zero = Empty
  Fin (succ k) = (Fin k) +₁ Unit

  module Fin-Basic where
    open Lt-Nat.Symbolic

    incl-succ : (k : Nat) → Fin k → Fin (succ k)
    incl-succ k fk = left fk

    last : (k : Nat) → Fin (succ k)
    last _ = right unit

    ind-Fk : {P : (k : Nat) → Fin k → Set} →
             (g : (k : Nat) → (x : Fin k) → P k x → P (succ k) (incl-succ k x)) →
             (p : (k : Nat) → P (succ k) (last k)) →
             (k : Nat) → (x : Fin k) → P k x
    ind-Fk g p zero ()
    ind-Fk g p (succ k) (left fk) = g k fk (ind-Fk g p k fk)
    ind-Fk g p (succ k) (right unit) = p k

    incl-Nat : (k : Nat) → Fin k → Nat
    incl-Nat k fk = ind-Fk (λ k x included-x → included-x) (λ k → k) k fk

    -- 7.3.5
    incl-Nat-bounded : {k : Nat} → (x : Fin k) → incl-Nat k x < k
    incl-Nat-bounded {zero} ()
    incl-Nat-bounded {succ k} (left fk) =
      Lt-Nat.trans (incl-Nat k fk) k (succ k)
        (incl-Nat-bounded fk) (Lt-Nat.lt-succ k)
    incl-Nat-bounded {succ k} (right unit) = Lt-Nat.lt-succ k

  -- exercise 7.7.a
  module classical-Fin-and-Fin where
    open Σ-Basic
    open ≡-Reasoning

    eq-biimpl-pr₁-eq : {k : Nat} → (x y : classical-Fin k) →
      (x ≡ y) ↔ (pr₁ x ≡ pr₁ y)
    eq-biimpl-pr₁-eq {zero} (pair k k<zero) = EmptyBasic.absurd (Lt-Nat.not-lt-zero k k<zero)
    eq-biimpl-pr₁-eq {succ k} x y = pair (forward x y) (backward x y)
      where
      forward : (x y : classical-Fin (succ k)) → (x ≡ y) → (pr₁ x ≡ pr₁ y)
      forward x y eq = ap pr₁ eq

      postulate backward : (x y : classical-Fin (succ k)) → (pr₁ x ≡ pr₁ y) → (x ≡ y)
