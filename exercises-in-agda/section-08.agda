open import Function.Base using (case_of_)

module _ where
  open import section-07 public

  open EmptyBasic
  open ≡-Basic

  -- definition 8.1.1
  Is-decidable : Set → Set
  Is-decidable A = A +₀ ¬ A

  Is-decidable-family : {A : Set} → (A → Set) → Set
  Is-decidable-family {A} B = (x : A) → Is-decidable (B x)

  -- a.k.a. booleanization
  decideInhabited : {A : Set} → Is-decidable A → Bool
  decideInhabited (left a) = true
  decideInhabited (right ¬a) = false

  reflectInhabitance : {A : Set} → (deca : Is-decidable A) → (decideInhabited deca ≡ true) → A
  reflectInhabitance (left a) _ = a
  reflectInhabitance (right ¬a) eq = absurd (Eq-Bool.false-neq-true (refl · eq))

  open Leq-Nat.Symbolic

  module Is-decidable where
    open ≡-Basic public

    -- example 8.1.2
    decideUnit : Is-decidable Unit
    decideUnit = left unit

    decideEmpty : Is-decidable Empty
    decideEmpty = right id

    -- example 8.1.3
    decide-+₀ : {A B : Set} → Is-decidable A → Is-decidable B → Is-decidable (A +₀ B)
    decide-+₀ (left a) (left b) = left (left a)
    decide-+₀ (left a) (right ¬b) = left (left a)
    decide-+₀ (right ¬a) (left b) = left (right b)
    decide-+₀ (right ¬a) (right ¬b) =
      right (λ {
        (left a) → ¬a a
      ; (right b) → ¬b b
      })

    decide-× : {A B : Set} → Is-decidable A → Is-decidable B → Is-decidable (A × B)
    decide-× (left a) (left b) = left (a , b)
    decide-× (left a) (right ¬b) = right (λ (a , b) → ¬b b)
    decide-× (right ¬a) (left b) = right (λ (a , b) → ¬a a)
    decide-× (right ¬a) (right ¬b) = right (λ (a , b) → ¬a a)

    decide-→ : {A B : Set} → Is-decidable A → Is-decidable B → Is-decidable (A → B)
    decide-→ (left a) (left b) = left (λ _ → b)
    decide-→ (left a) (right ¬b) = right (λ f → ¬b (f a))
    decide-→ (right ¬a) (left b) = left (λ a → absurd (¬a a))
    decide-→ (right ¬a) (right ¬b) = left (λ a → absurd (¬a a))

    -- example 8.1.4
    decideEqNat : (m n : Nat) → Is-decidable (Eq-Nat m n)
    decideEqNat zero zero = decideUnit
    decideEqNat zero (succ n) = decideEmpty
    decideEqNat (succ m) zero = decideEmpty
    decideEqNat (succ m) (succ n) = decideEqNat m n

    -- lemma 8.1.6
    biimpl-then-decidability-biimpl : {A B : Set} → (A ↔ B) → (Is-decidable A ↔ Is-decidable B)
    biimpl-then-decidability-biimpl (a→b , b→a) =
      (< a→b +₀ contrapose b→a > , < b→a +₀ contrapose a→b >)
      where open +₀-Basic

    -- proposition 8.2.3
    decide-⟶-with-dependent-decidability : {A B : Set} → Is-decidable A → (A → Is-decidable B) → Is-decidable (A → B)
    decide-⟶-with-dependent-decidability (left a) f = decide-→ (left a) (f a)
    decide-⟶-with-dependent-decidability (right ¬a) f = left (λ a → absurd (¬a a))

    -- proposition 8.2.3
    decide-×-with-dependent-decidability : {A B : Set} → Is-decidable A → (A → Is-decidable B) → Is-decidable (A × B)
    decide-×-with-dependent-decidability (left a) f = decide-× (left a) (f a)
    decide-×-with-dependent-decidability (right ¬a) f = right (λ (a , b) → ¬a a)

    -- exercise 8.2
    flatten : {A : Set} → Is-decidable (Is-decidable A) → Is-decidable A
    flatten (left dec) = dec
    flatten (right ¬dec) = right (λ a → ¬dec (left a))

  -- definition 8.1.5
  Has-decidable-eq : Set → Set
  Has-decidable-eq A = (x y : A) → Is-decidable (x ≡ y)

  module Has-decidable-eq where
    open Is-decidable
    open ≡-Reasoning

    -- exercise 8.6
    ×-deceq-biimpl-mutual-dependent-deceq : {A B : Set} → ((B → Has-decidable-eq A) × (A → Has-decidable-eq B)) ↔ Has-decidable-eq (A × B)
    ×-deceq-biimpl-mutual-dependent-deceq {A} {B} = (forward , backward)
      where
        forward : (B → Has-decidable-eq A) × (A → Has-decidable-eq B) → Has-decidable-eq (A × B)
        forward (f , g) (a1 , b1) (a2 , b2) =
          let deceqa = f b1
              deceqb = g a1
          in
            case (deceqa a1 a2) of λ {
              (left eqa) → case (deceqb b1 b2) of λ {
                (left eqb) → left (ap (λ e → e , b1) eqa · ap (λ e → a2 , e) eqb)
              ; (right ¬eqb) → right (λ paireq → ¬eqb (eq-×-then-pr₂-eq paireq))
              }
            ; (right ¬eqa) → right (λ paireq → ¬eqa (eq-then-pr₁-eq paireq))
            }

        backward : Has-decidable-eq (A × B) → (B → Has-decidable-eq A) × (A → Has-decidable-eq B)
        backward deceqab = (f , g)
          where
            f : B → Has-decidable-eq A
            f b a1 a2 =
              case (deceqab (a1 , b) (a2 , b)) of λ {
                (left eqab) → left (eq-then-pr₁-eq eqab)
              ; (right ¬eqab) → right (λ eqa → ¬eqab (ap (λ e → e , b) eqa))
              }
            g : A → Has-decidable-eq B
            g a b1 b2 =
              case (deceqab (a , b1) (a , b2)) of λ {
                (left eqab) → left (eq-×-then-pr₂-eq eqab)
              ; (right ¬eqab) → right (λ eqb → ¬eqab (ap (λ e → a , e) eqb))
              }

    -- proposition 8.1.7
    Nat-has-decidable-eq : Has-decidable-eq Nat
    Nat-has-decidable-eq m n = Σ.snd (biimpl-then-decidability-biimpl (Eq-Nat.Nat-≡-iff-Eq-Nat m n)) (decideEqNat m n)

    Unit-has-decidable-eq : Has-decidable-eq Unit
    Unit-has-decidable-eq unit unit = left refl

    -- proposition 8.1.8
    postulate Fin-has-decidable-eq : (k : Nat) → Has-decidable-eq (Fin k)

    open DivisibilityBasic.Symbolic
    -- theorem 8.1.9
    postulate divisibility-is-decidable : (d x : Nat) → Is-decidable (d ∣ x)

  -- TODO: formalize subsection 8.2

  -- definition 8.3.1
  Nat-is-lower-bound : {P : Nat → Set} (n : Nat) → Set
  Nat-is-lower-bound {P} n = (x : Nat) → P x → (n ≤ x)

  Nat-is-upper-bound : {P : Nat → Set} (n : Nat) → Set
  Nat-is-upper-bound {P} n = (x : Nat) → P x → (x ≤ n)

  -- TODO: formalize the rest of subsection 8.3
  -- TODO: formalize subsection 8.4
  -- TODO: formalize subsection 8.5

  -- TODO: exercise 8.1
  -- TODO: exercise 8.4
  -- TODO: exercise 8.5
  -- TODO: exercise 8.11
  -- TODO: exercise 8.12
  -- TODO: exercise 8.13
  -- TODO: exercise 8.14
  -- TODO: exercise 8.15

  -- exercise 8.7
  Eq-Copr : {A B : Set} → (A +₀ B) → (A +₀ B) → Set
  Eq-Copr (left a1) (left a2) = a1 ≡ a2
  Eq-Copr (left a1) (right b2) = Empty
  Eq-Copr (right b1) (left a2) = Empty
  Eq-Copr (right b1) (right b2) = b1 ≡ b2

  module Eq-Copr where
    open ≡-Basic public

    open Is-decidable
    open ≡-Reasoning
    open +₀-Basic

    Eq-Copr-refl : {A B : Set} → (x : A +₀ B) → Eq-Copr x x
    Eq-Copr-refl (left a) = refl
    Eq-Copr-refl (right b) = refl

    -- exercise 8.7.a
    Copr-≡-biimpl-Eq-Copr : {A B : Set} → {x y : A +₀ B} → (x ≡ y) ↔ (Eq-Copr x y)
    Copr-≡-biimpl-Eq-Copr {A} {B} {x} {y} = (forward x y , backward x y)
      where
        forward : (x y : A +₀ B) → (x ≡ y) → (Eq-Copr x y)
        forward x y refl = Eq-Copr-refl x

        backward : (x y : A +₀ B) → (Eq-Copr x y) → (x ≡ y)
        backward (left a1) (left a2) eq = ap left eq
        backward (left a1) (right b2) ()
        backward (right b1) (left a2) ()
        backward (right b1) (right b2) eq = ap right eq

    eq-copr-eq : {A B : Set} → {x y : A +₀ B} → (x ≡ y) → (Eq-Copr x y)
    eq-copr-eq eq = Σ.fst (Copr-≡-biimpl-Eq-Copr) eq

    obseq-then-eq : {A B : Set} → {x y : A +₀ B} → (Eq-Copr x y) → (x ≡ y)
    obseq-then-eq eq = Σ.snd (Copr-≡-biimpl-Eq-Copr) eq

    +₀-left-inj : {A : Set} → {B : Set} → {x y : A} → (left {A} {B} x ≡ left y) → (x ≡ y)
    +₀-left-inj eq = Σ.fst (Copr-≡-biimpl-Eq-Copr) eq

    +₀-right-inj : {A : Set} → {B : Set} → {x y : B} → (right {A} {B} x ≡ right y) → (x ≡ y)
    +₀-right-inj eq = Σ.fst (Copr-≡-biimpl-Eq-Copr) eq

    -- exercise 8.7.b
    +₀-deceq-biimpl-both-deceq : {A B : Set} → Has-decidable-eq (A +₀ B) ↔ ((Has-decidable-eq A) × (Has-decidable-eq B))
    +₀-deceq-biimpl-both-deceq {A} {B} = (forward , backward)
      where
        forward : Has-decidable-eq (A +₀ B) → ((Has-decidable-eq A) × (Has-decidable-eq B))
        forward deceqab = (f , g)
          where
            f : Has-decidable-eq A
            f a1 a2 =
              case (deceqab (left a1) (left a2)) of λ {
                (left eqla) → left (+₀-left-inj eqla)
              ; (right ¬eqla) → right (λ eqa → ¬eqla (ap left eqa))
              }
            g : Has-decidable-eq B
            g b1 b2 =
              case (deceqab (right b1) (right b2)) of λ {
                (left eqrb) → left (+₀-right-inj eqrb)
              ; (right ¬eqrb) → right (λ eqb → ¬eqrb (ap right eqb))
              }
        backward : ((Has-decidable-eq A) × (Has-decidable-eq B)) → Has-decidable-eq (A +₀ B)
        backward (deceqa , deceqb) (left a1) (left a2) =
          case (deceqa a1 a2) of λ {
            (left eqa) → left (ap left eqa)
          ; (right ¬eqa) → right (λ eqla → ¬eqa (+₀-left-inj eqla))
          }
        backward (deceqa , deceqb) (left a1) (right b2) = right (λ ())
        backward (deceqa , deceqb) (right b1) (left a2) = right (λ ())
        backward (deceqa , deceqb) (right b1) (right b2) =
          case (deceqb b1 b2) of λ {
            (left eqb) → left (ap right eqb)
          ; (right ¬eqb) → right (λ eqrb → ¬eqb (+₀-right-inj eqrb))
          }

    left-neq-right : {A : Set} → {B : Set} → {x : A} → {y : B} → ¬ (left x ≡ right y)
    left-neq-right lxry = Σ.fst Copr-≡-biimpl-Eq-Copr lxry

    right-neq-left : {A : Set} → {B : Set} → {x : A} → {y : B} → ¬ (right y ≡ left x)
    right-neq-left rylx = left-neq-right (inverse rylx)

  module _ where
    open Eq-Copr
    open Has-decidable-eq

    -- exercise 8.7.b
    Int-has-decidable-eq : Has-decidable-eq Int
    Int-has-decidable-eq = Σ.snd (+₀-deceq-biimpl-both-deceq) (Nat-has-decidable-eq , Σ.snd (+₀-deceq-biimpl-both-deceq) (Unit-has-decidable-eq , Nat-has-decidable-eq))

  -- exercise 8.8
  module exercise-8-8 {A : Set} {B : A → Set} where
    open Is-decidable

    i : Set
    i = Has-decidable-eq A

    ii : Set
    ii = (a : A) → Has-decidable-eq (B a)

    iii : Set
    iii = Has-decidable-eq (Σ A B)

    -- TODO: prove these (they seem to be really provable when A has a decidable equality)
    i-then-ii-biimpl-iii : i → ii ↔ iii
    i-then-ii-biimpl-iii deceq-a = (forward , backward)
      where
      postulate forward : ((a : A) → Has-decidable-eq (B a)) → Has-decidable-eq (Σ A B)
      -- forward a→deceq-ba (a1 , b1) (a2 , b2) =
      --   case (deceq-a a1 a2) of λ {
      --     (left refl) →
      --       case (a→deceq-ba a1 b1 b2) of λ {
      --         (left b1≡b2) → left (ap (pair a1) b1≡b2)
      --       ; (right b1≠b2) → right (λ paireq → b1≠b2 ({!   !}))
      --       }
      --   ; (right a1≠a2) → right (λ paireq → a1≠a2 (eq-then-pr₁-eq paireq))
      --   }

      postulate backward : Has-decidable-eq (Σ A B) → (a : A) → Has-decidable-eq (B a)
      -- backward deceq-pair a b1 b2 =
      --   case (deceq-pair (a , b1) (a , b2)) of λ {
      --     (left paireq) → left ({! !})
      --   ; (right ¬paireq) → right (λ b1≡b2 → ¬paireq (ap (pair a) b1≡b2))
      --   }

    section-and-iii-imply-i : (b : (x : A) → B x) → iii → i
    section-and-iii-imply-i b deceq-pair a1 a2 =
      case (deceq-pair (a1 , b a1) (a2 , b a2)) of λ {
        (left paireq) → left (eq-then-pr₁-eq paireq)
      ; (right ¬paireq) → right (λ { refl → ¬paireq refl })
      }

  -- exercise 8.9
  module exercise-8-9 where
    open Is-decidable
    open ≡-Reasoning
    open Fin-Basic

    -- exercise 8.9.a
    decideFinDepfn : {k : Nat} → {B : Fin k → Set} → Is-decidable-family B → Is-decidable ((x : Fin k) → B x)
    decideFinDepfn {zero} _ = left λ { () }
    decideFinDepfn {succ k} {B} decide-bx =
      let B' = λ (x : Fin k) → B (incl-succ x)
          decide-x→b'x : Is-decidable ((x : Fin k) → B' x)
          decide-x→b'x = decideFinDepfn (λ (x : Fin k) → decide-bx (incl-succ x))
      in case decide-x→b'x of λ {
        (left f') →
          case (decide-bx last) of λ {
            (left last-b) → left (λ { (left x') → f' x' ; (right unit) → last-b })
          ; (right ¬last-b) → right (λ f → ¬last-b (f last))
          }
      ; (right ¬f') → right (λ f → ¬f' (λ x' → f (incl-succ x')))
      }

    -- I think the use of this postulate is essential both in the base case and the inductive part
    -- (i.e. some restricted version of funext would be equivalent to deceqFinDepfn)
    postulate funext : {A : Set} → {B : A → Set} → {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g

    -- exercise 8.9.b
    deceqFinDepfn : {k : Nat} → {B : Fin k → Set} → ((x : Fin k) → Has-decidable-eq (B x)) → Has-decidable-eq ((x : Fin k) → B x)
    deceqFinDepfn {zero} _ f1 f2 = left (funext λ { () })
    deceqFinDepfn {succ k} {B} x→deceq-bx f1 f2 =
      case deceq-x'→b'x' (λ x' → f1 (incl-succ x')) (λ x' → f2 (incl-succ x')) of λ {
        (left f1'≡f2') →
          case (x→deceq-bx last (f1 last) (f2 last)) of λ {
            (left f1-last≡f2-last) → left (funext λ { (left x') → ap (λ e → e x') f1'≡f2'; (right unit) → f1-last≡f2-last })
          ; (right ¬f1-last≡f2-last) → right (λ { refl → ¬f1-last≡f2-last refl })
          }
        ; (right ¬f1'≡f2') → right (λ { refl → ¬f1'≡f2' refl })
      }
        where
        B' = λ (x : Fin k) → B (incl-succ x)
        deceq-x'→b'x' : Has-decidable-eq ((x : Fin k) → B' x)
        deceq-x'→b'x' = deceqFinDepfn (λ x → x→deceq-bx (incl-succ x))

  module _ where
    open Is-decidable
    open ≡-Reasoning
    open Fin-Basic
  
    -- exercise 8.3
    Fin-de-Morgan : {k : Nat} → {P : Fin k → Set} → Is-decidable-family P → ¬ ((x : Fin k) → P x) → Σ (Fin k) (λ x → ¬ P x)
    Fin-de-Morgan {zero} decide-p ¬ΠP = absurd (¬ΠP λ { () })
    Fin-de-Morgan {succ k} {P} decide-p ¬ΠP =
      case decide-p last of λ {
        (left plast) →
          let P'        = λ (x : Fin k) → P (incl-succ x)
              decide-P' = λ (x : Fin k) → decide-p (incl-succ x)
              ¬ΠP' ΠP'  = ¬ΠP λ { (left x) → ΠP' x ; (right unit) → plast }
          in case (Fin-de-Morgan {k} decide-P' ¬ΠP') of λ { (x , ¬Px) → (incl-succ x , ¬Px) }
      ; (right ¬plast) → last , ¬plast
      }

  open Leq-Nat
  open Lt-Nat.Symbolic

  searchDescendingFromNat : {P : Nat → Set} → {decide-p : Is-decidable-family P} → (N : Nat) →
                                Σ Nat (λ n → -- found a value n
                                  P n ×     -- that satisfies P
                                  (n ≤ N) × -- and is less than or equal to N
                                  ((x : Nat) → P x → (x ≤ n) +₀ (N < x))  -- such that for any x with (P x), x does not lie in (succ n)..N
                                ) +₀ ((x : Nat) → (x ≤ N) → ¬ P x) -- Or, not found in 0..N
  searchDescendingFromNat {P} {decide-p} zero =
    case decide-p zero of λ {
      (left pz) → left (zero , (pz , Leq-Nat.Leq-Nat-refl zero , λ x _ → Lt-Nat.leq-or-gt x zero))
    ; (right ¬pz) → right λ { zero _ → ¬pz; (succ k) () }
    }
  searchDescendingFromNat {P} {decide-p} (succ N) =
    case decide-p (succ N) of λ {
      (left psN) →
        left (
          succ N ,
          (psN , Leq-Nat.Leq-Nat-refl (succ N) , λ x _ → Lt-Nat.leq-or-gt x (succ N))
        )
    ; (right ¬psN) →
      case (searchDescendingFromNat {P} {decide-p} N) of λ {
        (left (n , (pn , leq-n , any-satisfying-Nat-is-≤n-or-N<))) →
          left (
            n ,
            (pn , trans n N (succ N) leq-n (self-succ N) , λ x px →
              +₀-Basic.mapRightOf (any-satisfying-Nat-is-≤n-or-N< x px) (λ N<x → 
                case Σ.snd (Lt-Nat.lt-or-eq-iff-leq (succ N) x) (Σ.fst (Lt-Nat.lt-iff-succ-leq N x) N<x) of λ {
                  (left sN<x) → sN<x
                ; (right refl) → absurd (¬psN px)
                }
              )
            )
          )
      ; (right ¬pn-below-N) →
          right (λ n n≤sN → by-comparing n N λ {
            (left n≤N) → ¬pn-below-N n n≤N
          ; (right N≤n) →
            case (leq-succ-then-leq-or-eq-succ n N n≤sN) of λ {
              (left n≤N) → ¬pn-below-N n n≤N
            ; (right refl) → ¬psN
            }
          })
      }
    }

  module exercise-8-10 {P : Nat → Set} {decide-p : Is-decidable-family P} {m : Nat} {mub : Nat-is-upper-bound {P} m} where
    open Is-decidable
    open ≡-Reasoning
    open Fin-Basic

    -- exercise 8.10.a
    decide-Σ-P : Is-decidable (Σ Nat P)
    decide-Σ-P =
      case (searchDescendingFromNat {P} {decide-p} m) of λ {
        (left (n , (pn , leq-n , _))) → left (n , pn)
      ; (right ¬pn-below-m) → right (λ (n , pn) → ¬pn-below-m n (mub n pn) pn)
      }

    -- exercise 8.10.b
    maximize : Σ Nat P → Σ Nat (λ n → P n × Nat-is-upper-bound {P} n)
    maximize (n , pn) =
      case (searchDescendingFromNat {P} {decide-p} m) of λ {
        (left (m' , (pm' , m'≤m , no-value-from-sm'-upto-m-satisfies))) →
          (m' , pm' , (λ m'' pm'' →
            -- goal : m'' ≤ m'
            Lt-Nat.by-comparing m'' m' λ {
              (left (left m''<m')) → Lt-Nat.as-leq m'' m' m''<m'
            ; (left (right refl)) → Leq-Nat.Leq-Nat-refl m''
            ; (right m'<m'') →
              case (no-value-from-sm'-upto-m-satisfies m'' pm'') of λ {
                (left m''≤m') → m''≤m'
              ; (right m<m'') → absurd (Σ.fst (Lt-Nat.lt-iff-not-flip-leq m m'') m<m'' (mub m'' pm'')) -- impossible
              }
          }))
      ; (right ¬pm'-below-m) → absurd (¬pm'-below-m n (mub n pn) pn) -- impossible
      }
 
    -- TODO: exercise 8.10.c
