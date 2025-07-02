open import Function.Base using (case_of_)

module _ where
  open import section-06 public

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
    divides-refl m = (one , mul-runit m)

    -- 7.1.4
    one-divides-any : (m : Nat) → one ∣ m
    one-divides-any m = (m , mul-lunit m)

    -- 7.1.5
    divides-both-then-divides-sum : (d x y : Nat) → d ∣ x → d ∣ y → d ∣ (x + y)
    divides-both-then-divides-sum d x y (k , p) (l , q) =
      (
        k + l ,
        (begin
          d * (k + l)     ≡⟨ mul-ldistr d k l ⟩
          d * k + d * l   ≡⟨ ap (λ e → e + d * l) p ⟩
          x + d * l       ≡⟨ ap (λ e → x + e) q ⟩
          x + y           ∎)
      )
    
    -- TODO: prove, as part of 7.1
    postulate divides-summand-and-sum-then-divides-other : (d x y : Nat) → d ∣ x → d ∣ (x + y) → d ∣ y

    -- TODO: exercise 7.2

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

    incl-succ : {k : Nat} → Fin k → Fin (succ k)
    incl-succ fk = left fk

    last : {k : Nat} → Fin (succ k)
    last = right unit

    ind-Fk : {P : (k : Nat) → Fin k → Set} →
             (g : (k : Nat) → (x : Fin k) → P k x → P (succ k) (incl-succ x)) →
             (p : (k : Nat) → P (succ k) last) →
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

    zero-Fin : {k : Nat} → Fin (succ k)
    zero-Fin {zero} = right unit
    zero-Fin {succ k} = incl-succ (zero-Fin {k})

    skip-zero : {k : Nat} → Fin k → Fin (succ k)
    skip-zero {succ k} (left x) = incl-succ (skip-zero {k} x)
    skip-zero {succ k} (right unit) = last

    succ-Fin : {k : Nat} → Fin k → Fin k
    succ-Fin {succ k} (left x) = skip-zero x
    succ-Fin {succ k} (right unit) = zero-Fin

  Eq-Fin : (k : Nat) → Fin k → Fin k → Set
  Eq-Fin zero () ()
  Eq-Fin (succ k) (left x) (left y) = Eq-Fin k x y
  Eq-Fin (succ k) (left x) (right unit) = Empty
  Eq-Fin (succ k) (right unit) (left y) = Empty
  Eq-Fin (succ k) (right unit) (right unit) = Unit

  -- exercise 7.5
  module Eq-Fin where
    open Fin-Basic
    open ≡-Basic public
    open ≡-Reasoning
    open EmptyBasic

    Eq-Fin-refl : {k : Nat} → (x : Fin k) → Eq-Fin k x x
    Eq-Fin-refl {zero} ()
    Eq-Fin-refl {succ k} (left x) = Eq-Fin-refl x
    Eq-Fin-refl {succ k} (right unit) = unit

    Fin-≡-biimpl-Eq-Fin : {k : Nat} → (x y : Fin k) → (x ≡ y) ↔ (Eq-Fin k x y)
    Fin-≡-biimpl-Eq-Fin {zero} () ()
    Fin-≡-biimpl-Eq-Fin {succ k} x y = ((λ { refl → Eq-Fin-refl x }), backward x y)
      where
      backward : (x y : Fin (succ k)) → (Eq-Fin (succ k) x y) → (x ≡ y)
      backward (left x) (left y) eq-fin = ap left ((Fin-≡-biimpl-Eq-Fin {k} x y).Σ.snd eq-fin)
      backward (left x) (right unit) ()
      backward (right unit) (left y) ()
      backward (right unit) (right unit) eq-fin = refl

    postulate incl-succ-inj : {k : Nat} → {x y : Fin k} → (incl-succ x ≡ incl-succ y) → (x ≡ y)
    postulate succ-non-last-neq-zero : {k : Nat} → {x : Fin k} → ¬ (succ-Fin (incl-succ x) ≡ zero-Fin)
    postulate succ-inj : {k : Nat} → {x y : Fin k} → (succ-Fin x ≡ succ-Fin y) → (x ≡ y)

  module classical-Fin-and-Fin where
    open Σ-Basic
    open ≡-Reasoning

    -- exercise 7.7.a
    eq-biimpl-pr₁-eq : {k : Nat} → (x y : classical-Fin k) → (x ≡ y) ↔ (pr₁ x ≡ pr₁ y)
    eq-biimpl-pr₁-eq {zero} (k , k<zero) = EmptyBasic.absurd (Lt-Nat.not-lt-zero k k<zero)
    eq-biimpl-pr₁-eq {succ k} (x , x<sk) (y , y<sk) =
      (
        eq-implies-pr₁-eq ,
        (λ { refl → case (Lt-Nat.subsingleton x (succ k) x<sk y<sk) of λ { refl → refl }})
      )

    -- TODO: exercise 7.7.b
