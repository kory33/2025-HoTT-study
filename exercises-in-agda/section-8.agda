open import Function.Base using (case_of_)

module _ where
  open import section-7 public

  open EmptyBasic
  open ≡-Basic

  Is-decidable : Set → Set
  Is-decidable A = A +₁ ¬ A

  Has-decidable-eq : Set → Set
  Has-decidable-eq A = (x y : A) → Is-decidable (x ≡ y)

  -- a.k.a. booleanization
  decide-inhabited : {A : Set} → Is-decidable A → Bool
  decide-inhabited (left a) = true
  decide-inhabited (right ¬a) = false

  reflect-inhabitance : {A : Set} → (deca : Is-decidable A) → (decide-inhabited deca ≡ true) → A
  reflect-inhabitance (left a) _ = a
  reflect-inhabitance (right ¬a) eq = absurd (Eq-Bool.false-neq-true (refl · eq))

  module Is-decidable where
    open ≡-Basic public

    decide-Unit : Is-decidable Unit
    decide-Unit = left unit

    decide-Empty : Is-decidable Empty
    decide-Empty = right id

    decide-+₁ : {A B : Set} → Is-decidable A → Is-decidable B → Is-decidable (A +₁ B)
    decide-+₁ (left a) (left b) = left (left a)
    decide-+₁ (left a) (right ¬b) = left (left a)
    decide-+₁ (right ¬a) (left b) = left (right b)
    decide-+₁ (right ¬a) (right ¬b) =
      right (λ {
        (left a) → ¬a a
      ; (right b) → ¬b b
      })

    decide-× : {A B : Set} → Is-decidable A → Is-decidable B → Is-decidable (A × B)
    decide-× (left a) (left b) = left (pair a b)
    decide-× (left a) (right ¬b) = right (λ (pair a b) → ¬b b)
    decide-× (right ¬a) (left b) = right (λ (pair a b) → ¬a a)
    decide-× (right ¬a) (right ¬b) = right (λ (pair a b) → ¬a a)

    decide-→ : {A B : Set} → Is-decidable A → Is-decidable B → Is-decidable (A → B)
    decide-→ (left a) (left b) = left (λ _ → b)
    decide-→ (left a) (right ¬b) = right (λ f → ¬b (f a))
    decide-→ (right ¬a) (left b) = left (λ a → absurd (¬a a))
    decide-→ (right ¬a) (right ¬b) = left (λ a → absurd (¬a a))

    decide-Eq-Nat : (m n : Nat) → Is-decidable (Eq-Nat m n)
    decide-Eq-Nat zero zero = decide-Unit
    decide-Eq-Nat zero (succ n) = decide-Empty
    decide-Eq-Nat (succ m) zero = decide-Empty
    decide-Eq-Nat (succ m) (succ n) = decide-Eq-Nat m n

    module _ where
      open +₁-Basic
      decide-biimpl : {A B : Set} → (A ↔ B) → (Is-decidable A ↔ Is-decidable B)
      decide-biimpl (pair a→b b→a) = pair (< a→b +₁ contrapose b→a >) (< b→a +₁ contrapose a→b >)

    Nat-has-decidable-eq : Has-decidable-eq Nat
    Nat-has-decidable-eq m n = (decide-biimpl (Eq-Nat.Nat-≡-biimpl-Eq-Nat m n)).Σ.snd (decide-Eq-Nat m n)

    decide-⟶-with-dependent-decidability : {A B : Set} → Is-decidable A → (A → Is-decidable B) → Is-decidable (A → B)
    decide-⟶-with-dependent-decidability (left a) f = decide-→ (left a) (f a)
    decide-⟶-with-dependent-decidability (right ¬a) f = left (λ a → absurd (¬a a))

    decide-×-with-dependent-decidability : {A B : Set} → Is-decidable A → (A → Is-decidable B) → Is-decidable (A × B)
    decide-×-with-dependent-decidability (left a) f = decide-× (left a) (f a)
    decide-×-with-dependent-decidability (right ¬a) f = right (λ (pair a b) → ¬a a)

    -- exercise 8.2
    flatten : {A : Set} → Is-decidable (Is-decidable A) → Is-decidable A
    flatten (left dec) = dec
    flatten (right ¬dec) = right (λ a → ¬dec (left a))

  module Has-decidable-eq where
    open Is-decidable
    open ≡-Reasoning

    -- exercise 8.6
    ×-deceq-biimpl-mutual-dependent-deceq : {A B : Set} → ((B → Has-decidable-eq A) × (A → Has-decidable-eq B)) ↔ Has-decidable-eq (A × B)
    ×-deceq-biimpl-mutual-dependent-deceq {A} {B} = pair forward backward
      where
        forward : (B → Has-decidable-eq A) × (A → Has-decidable-eq B) → Has-decidable-eq (A × B)
        forward (pair f g) (pair a1 b1) (pair a2 b2) =
          let deceqa = f b1
              deceqb = g a1
          in
            case (deceqa a1 a2) of λ {
              (left eqa) → case (deceqb b1 b2) of λ {
                (left eqb) → left (ap (λ e → pair e b1) eqa · ap (λ e → pair a2 e) eqb)
              ; (right ¬eqb) → right (λ paireq → ¬eqb (eq-×-implies-pr₂-eq paireq))
              }
            ; (right ¬eqa) → right (λ paireq → ¬eqa (eq-implies-pr₁-eq paireq))
            }

        backward : Has-decidable-eq (A × B) → (B → Has-decidable-eq A) × (A → Has-decidable-eq B)
        backward deceqab = pair f g
          where
            f : B → Has-decidable-eq A
            f b a1 a2 =
              case (deceqab (pair a1 b) (pair a2 b)) of λ {
                (left eqab) → left (eq-implies-pr₁-eq eqab)
              ; (right ¬eqab) → right (λ eqa → ¬eqab (ap (λ e → pair e b) eqa))
              }
            g : A → Has-decidable-eq B
            g a b1 b2 =
              case (deceqab (pair a b1) (pair a b2)) of λ {
                (left eqab) → left (eq-×-implies-pr₂-eq eqab)
              ; (right ¬eqab) → right (λ eqb → ¬eqab (ap (λ e → pair a e) eqb))
              }

  -- exercise 8.7
  Eq-Copr : {A B : Set} → (A +₁ B) → (A +₁ B) → Set
  Eq-Copr (left a1) (left a2) = a1 ≡ a2
  Eq-Copr (left a1) (right b2) = Empty
  Eq-Copr (right b1) (left a2) = Empty
  Eq-Copr (right b1) (right b2) = b1 ≡ b2

  module Eq-Copr where
    open ≡-Basic public

    open Is-decidable
    open ≡-Reasoning
    open +₁-Basic

    Eq-Copr-refl : {A B : Set} → (x : A +₁ B) → Eq-Copr x x
    Eq-Copr-refl (left a) = refl
    Eq-Copr-refl (right b) = refl

    Copr-≡-biimpl-Eq-Copr : {A B : Set} → {x y : A +₁ B} → (x ≡ y) ↔ (Eq-Copr x y)
    Copr-≡-biimpl-Eq-Copr {A} {B} {x} {y} = pair (forward x y) (backward x y)
      where
        forward : (x y : A +₁ B) → (x ≡ y) → (Eq-Copr x y)
        forward x y refl = Eq-Copr-refl x

        backward : (x y : A +₁ B) → (Eq-Copr x y) → (x ≡ y)
        backward (left a1) (left a2) eq = ap left eq
        backward (left a1) (right b2) ()
        backward (right b1) (left a2) ()
        backward (right b1) (right b2) eq = ap right eq

    +₁-left-inj : {A : Set} → {B : Set} → {x y : A} → (left {A} {B} x ≡ left y) → (x ≡ y)
    +₁-left-inj eq = (Copr-≡-biimpl-Eq-Copr).Σ.fst eq

    +₁-right-inj : {A : Set} → {B : Set} → {x y : B} → (right {A} {B} x ≡ right y) → (x ≡ y)
    +₁-right-inj eq = (Copr-≡-biimpl-Eq-Copr).Σ.fst eq

    +₁-deceq-biimpl-both-deceq : {A B : Set} → ((Has-decidable-eq A) × (Has-decidable-eq B)) ↔ Has-decidable-eq (A +₁ B)
    +₁-deceq-biimpl-both-deceq {A} {B} = pair forward backward
      where
        forward : ((Has-decidable-eq A) × (Has-decidable-eq B)) → Has-decidable-eq (A +₁ B)
        forward (pair deceqa deceqb) (left a1) (left a2) =
          case (deceqa a1 a2) of λ {
            (left eqa) → left (ap left eqa)
          ; (right ¬eqa) → right (λ eqla → ¬eqa (+₁-left-inj eqla))
          }
        forward (pair deceqa deceqb) (left a1) (right b2) = right (λ ())
        forward (pair deceqa deceqb) (right b1) (left a2) = right (λ ())
        forward (pair deceqa deceqb) (right b1) (right b2) =
          case (deceqb b1 b2) of λ {
            (left eqb) → left (ap right eqb)
          ; (right ¬eqb) → right (λ eqrb → ¬eqb (+₁-right-inj eqrb))
          }

        backward : Has-decidable-eq (A +₁ B) → ((Has-decidable-eq A) × (Has-decidable-eq B))
        backward deceqab = pair f g
          where
            f : Has-decidable-eq A
            f a1 a2 =
              case (deceqab (left a1) (left a2)) of λ {
                (left eqla) → left (+₁-left-inj eqla)
              ; (right ¬eqla) → right (λ eqa → ¬eqla (ap left eqa))
              }
            g : Has-decidable-eq B
            g b1 b2 =
              case (deceqab (right b1) (right b2)) of λ {
                (left eqrb) → left (+₁-right-inj eqrb)
              ; (right ¬eqrb) → right (λ eqb → ¬eqrb (ap right eqb))
              }

  postulate Int-has-decidable-eq : Has-decidable-eq Int

  Eq-Σ : {A : Set} → {B : A → Set} → (Σ A B) → (Σ A B) → Set
  Eq-Σ (pair a1 b1) (pair a2 b2) = Σ (a1 ≡ a2) (λ { (refl) → b1 ≡ b2 })

  module Eq-Σ where
    open ≡-Basic public
    open EmptyBasic
    open Is-decidable
    open ≡-Reasoning
    open Σ-Basic

  module exercise-8-8 {A : Set} {B : A → Set} where
    open Is-decidable

    i : Set
    i = Has-decidable-eq A

    ii : Set
    ii = (a : A) → Has-decidable-eq (B a)

    iii : Set
    iii = Has-decidable-eq (Σ A B)

    i-then-ii-biimpl-iii : i → ii ↔ iii
    i-then-ii-biimpl-iii deceq-a = pair forward backward
      where
      forward : ((a : A) → Has-decidable-eq (B a)) → Has-decidable-eq (Σ A B)
      forward a→deceq-ba (pair a1 b1) (pair a2 b2) =
        case (deceq-a a1 a2) of λ {
          (left refl) →
            case (a→deceq-ba a1 b1 b2) of λ {
              (left b1≡b2) → left (ap (pair a1) b1≡b2)
            ; (right b1≠b2) → right (λ paireq → b1≠b2 ({!   !}))
            }
        ; (right a1≠a2) → right (λ paireq → a1≠a2 (eq-implies-pr₁-eq paireq))
        }
      backward : Has-decidable-eq (Σ A B) → (a : A) → Has-decidable-eq (B a)
      backward deceq-pair a b1 b2 =
        case (deceq-pair (pair a b1) (pair a b2)) of λ {
          (left eqpair) → left {!   !}
        ; (right ¬eqpair) → right (λ b1≡b2 → ¬eqpair (ap (pair a) b1≡b2))
        }

    section-and-iii-imply-i : (b : (x : A) → B x) → iii → i
    section-and-iii-imply-i b deceq-pair a1 a2 =
      case (deceq-pair (pair a1 (b a1)) (pair a2 (b a2))) of λ {
        (left paireq) → left (eq-implies-pr₁-eq paireq)
      ; (right ¬paireq) → right (λ { refl → ¬paireq refl })
      }
