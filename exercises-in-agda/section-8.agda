open import Function.Base using (case_of_)

module _ where
  open import section-7 public

  open EmptyBasic
  open ≡-Basic

  Is-decidable : Set → Set
  Is-decidable A = A +₁ ¬ A

  Has-decidable-eq : Set → Set
  Has-decidable-eq A = (x y : A) → Is-decidable (x ≡ y)

  Is-decidable-family : {A : Set} → (A → Set) → Set
  Is-decidable-family {A} B = (x : A) → Is-decidable (B x)

  -- a.k.a. booleanization
  decide-inhabited : {A : Set} → Is-decidable A → Bool
  decide-inhabited (left a) = true
  decide-inhabited (right ¬a) = false

  reflect-inhabitance : {A : Set} → (deca : Is-decidable A) → (decide-inhabited deca ≡ true) → A
  reflect-inhabitance (left a) _ = a
  reflect-inhabitance (right ¬a) eq = absurd (Eq-Bool.false-neq-true (refl · eq))

  open Leq-Nat.Symbolic
  Nat-is-lower-bound : {P : Nat → Set} (n : Nat) → Set
  Nat-is-lower-bound {P} n = (x : Nat) → P x → (n ≤ x)

  Nat-is-upper-bound : {P : Nat → Set} (n : Nat) → Set
  Nat-is-upper-bound {P} n = (x : Nat) → P x → (x ≤ n)

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
    decide-× (left a) (left b) = left (a , b)
    decide-× (left a) (right ¬b) = right (λ (a , b) → ¬b b)
    decide-× (right ¬a) (left b) = right (λ (a , b) → ¬a a)
    decide-× (right ¬a) (right ¬b) = right (λ (a , b) → ¬a a)

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
      decide-biimpl (a→b , b→a) = (< a→b +₁ contrapose b→a > , < b→a +₁ contrapose a→b >)

    decide-⟶-with-dependent-decidability : {A B : Set} → Is-decidable A → (A → Is-decidable B) → Is-decidable (A → B)
    decide-⟶-with-dependent-decidability (left a) f = decide-→ (left a) (f a)
    decide-⟶-with-dependent-decidability (right ¬a) f = left (λ a → absurd (¬a a))

    decide-×-with-dependent-decidability : {A B : Set} → Is-decidable A → (A → Is-decidable B) → Is-decidable (A × B)
    decide-×-with-dependent-decidability (left a) f = decide-× (left a) (f a)
    decide-×-with-dependent-decidability (right ¬a) f = right (λ (a , b) → ¬a a)

    -- exercise 8.2
    flatten : {A : Set} → Is-decidable (Is-decidable A) → Is-decidable A
    flatten (left dec) = dec
    flatten (right ¬dec) = right (λ a → ¬dec (left a))

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
              ; (right ¬eqb) → right (λ paireq → ¬eqb (eq-×-implies-pr₂-eq paireq))
              }
            ; (right ¬eqa) → right (λ paireq → ¬eqa (eq-implies-pr₁-eq paireq))
            }

        backward : Has-decidable-eq (A × B) → (B → Has-decidable-eq A) × (A → Has-decidable-eq B)
        backward deceqab = (f , g)
          where
            f : B → Has-decidable-eq A
            f b a1 a2 =
              case (deceqab (a1 , b) (a2 , b)) of λ {
                (left eqab) → left (eq-implies-pr₁-eq eqab)
              ; (right ¬eqab) → right (λ eqa → ¬eqab (ap (λ e → e , b) eqa))
              }
            g : A → Has-decidable-eq B
            g a b1 b2 =
              case (deceqab (a , b1) (a , b2)) of λ {
                (left eqab) → left (eq-×-implies-pr₂-eq eqab)
              ; (right ¬eqab) → right (λ eqb → ¬eqab (ap (λ e → a , e) eqb))
              }

    Nat-has-decidable-eq : Has-decidable-eq Nat
    Nat-has-decidable-eq m n = (decide-biimpl (Eq-Nat.Nat-≡-biimpl-Eq-Nat m n)).Σ.snd (decide-Eq-Nat m n)

    Unit-has-decidable-eq : Has-decidable-eq Unit
    Unit-has-decidable-eq unit unit = left refl

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
    Copr-≡-biimpl-Eq-Copr {A} {B} {x} {y} = (forward x y , backward x y)
      where
        forward : (x y : A +₁ B) → (x ≡ y) → (Eq-Copr x y)
        forward x y refl = Eq-Copr-refl x

        backward : (x y : A +₁ B) → (Eq-Copr x y) → (x ≡ y)
        backward (left a1) (left a2) eq = ap left eq
        backward (left a1) (right b2) ()
        backward (right b1) (left a2) ()
        backward (right b1) (right b2) eq = ap right eq

    obseq-then-eq : {A B : Set} → {x y : A +₁ B} → (Eq-Copr x y) → (x ≡ y)
    obseq-then-eq eq = (Copr-≡-biimpl-Eq-Copr).Σ.snd eq

    +₁-left-inj : {A : Set} → {B : Set} → {x y : A} → (left {A} {B} x ≡ left y) → (x ≡ y)
    +₁-left-inj eq = (Copr-≡-biimpl-Eq-Copr).Σ.fst eq

    +₁-right-inj : {A : Set} → {B : Set} → {x y : B} → (right {A} {B} x ≡ right y) → (x ≡ y)
    +₁-right-inj eq = (Copr-≡-biimpl-Eq-Copr).Σ.fst eq

    +₁-deceq-biimpl-both-deceq : {A B : Set} → Has-decidable-eq (A +₁ B) ↔ ((Has-decidable-eq A) × (Has-decidable-eq B))
    +₁-deceq-biimpl-both-deceq {A} {B} = (forward , backward)
      where
        forward : Has-decidable-eq (A +₁ B) → ((Has-decidable-eq A) × (Has-decidable-eq B))
        forward deceqab = (f , g)
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
        backward : ((Has-decidable-eq A) × (Has-decidable-eq B)) → Has-decidable-eq (A +₁ B)
        backward (deceqa , deceqb) (left a1) (left a2) =
          case (deceqa a1 a2) of λ {
            (left eqa) → left (ap left eqa)
          ; (right ¬eqa) → right (λ eqla → ¬eqa (+₁-left-inj eqla))
          }
        backward (deceqa , deceqb) (left a1) (right b2) = right (λ ())
        backward (deceqa , deceqb) (right b1) (left a2) = right (λ ())
        backward (deceqa , deceqb) (right b1) (right b2) =
          case (deceqb b1 b2) of λ {
            (left eqb) → left (ap right eqb)
          ; (right ¬eqb) → right (λ eqrb → ¬eqb (+₁-right-inj eqrb))
          }

    left-neq-right : {A : Set} → {B : Set} → {x : A} → {y : B} → ¬ (left x ≡ right y)
    left-neq-right lxry = (Copr-≡-biimpl-Eq-Copr .Σ.fst) lxry

  module _ where
    open Eq-Copr
    open Has-decidable-eq

    Int-has-decidable-eq : Has-decidable-eq Int
    Int-has-decidable-eq = (+₁-deceq-biimpl-both-deceq).Σ.snd (Nat-has-decidable-eq , (+₁-deceq-biimpl-both-deceq).Σ.snd (Unit-has-decidable-eq , Nat-has-decidable-eq))

  Eq-Σ : {A : Set} → {B : A → Set} → (Σ A B) → (Σ A B) → Set
  Eq-Σ (a1 , b1) (a2 , b2) = Σ (a1 ≡ a2) (λ { (refl) → b1 ≡ b2 })

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
      --   ; (right a1≠a2) → right (λ paireq → a1≠a2 (eq-implies-pr₁-eq paireq))
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
        (left paireq) → left (eq-implies-pr₁-eq paireq)
      ; (right ¬paireq) → right (λ { refl → ¬paireq refl })
      }

  module exercise-8-9 where
    open Is-decidable
    open ≡-Reasoning
    open Fin-Basic

    decide-Fin-depfn : {k : Nat} → {B : Fin k → Set} → Is-decidable-family B → Is-decidable ((x : Fin k) → B x)
    decide-Fin-depfn {zero} _ = left λ { () }
    decide-Fin-depfn {succ k} {B} decide-bx =
      let B' = λ (x : Fin k) → B (incl-succ x)
          decide-x→b'x : Is-decidable ((x : Fin k) → B' x)
          decide-x→b'x = decide-Fin-depfn (λ (x : Fin k) → decide-bx (incl-succ x))
      in case decide-x→b'x of λ {
        (left f') →
          case (decide-bx last) of λ {
            (left last-b) → left (λ { (left x') → f' x' ; (right unit) → last-b })
          ; (right ¬last-b) → right (λ f → ¬last-b (f last))
          }
      ; (right ¬f') → right (λ f → ¬f' (λ x' → f (incl-succ x')))
      }

    -- I think the use of this postulate is essential both in the base case and the inductive part
    -- (i.e. some restricted version of funext would be equivalent to deceq-Fin-depfn)
    postulate funext : {A : Set} → {B : A → Set} → {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g

    deceq-Fin-depfn : {k : Nat} → {B : Fin k → Set} → ((x : Fin k) → Has-decidable-eq (B x)) → Has-decidable-eq ((x : Fin k) → B x)
    deceq-Fin-depfn {zero} _ f1 f2 = left (funext λ { () })
    deceq-Fin-depfn {succ k} {B} x→deceq-bx f1 f2 =
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
        deceq-x'→b'x' = deceq-Fin-depfn (λ x → x→deceq-bx (incl-succ x))

  module exercise-8-3 where
    open Is-decidable
    open ≡-Reasoning
    open Fin-Basic
  
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

  module _ where
    open Leq-Nat
    open Lt-Nat.Symbolic

    search-descending-from-Nat : {P : Nat → Set} → {decide-p : Is-decidable-family P} → (N : Nat) →
                                 Σ Nat (λ n → -- found a value n
                                    P n ×     -- that satisfies P
                                    (n ≤ N) × -- and is less than or equal to N
                                    ((x : Nat) → P x → (x ≤ n) +₁ (N < x)  -- such that for any x with (P x), x does not lie in (succ n)..N
                                 )) +₁ ((x : Nat) → (x ≤ N) → ¬ P x) -- Or, not found in 0..N
    search-descending-from-Nat {P} {decide-p} zero =
      case decide-p zero of λ {
        (left pz) → left (zero , (pz , Leq-Nat.Leq-Nat-refl zero), (λ x _ → Lt-Nat.leq-or-gt x zero))
      ; (right ¬pz) → right λ { zero _ → ¬pz; (succ k) () }
      }
    search-descending-from-Nat {P} {decide-p} (succ N) =
      case decide-p (succ N) of λ {
        (left psN) →
          left (
            succ N ,
            (psN , Leq-Nat.Leq-Nat-refl (succ N)),
            (λ x _ → Lt-Nat.leq-or-gt x (succ N))
          )
      ; (right ¬psN) →
        case (search-descending-from-Nat {P} {decide-p} N) of λ {
          (left (n , (pn , leq-n), any-satisfying-Nat-is-≤n-or-N<)) →
            left (
              n ,
              (pn , trans n N (succ N) leq-n (self-succ N)),
              (λ x px →
                +₁-Basic.mapRightOf (any-satisfying-Nat-is-≤n-or-N< x px) (λ N<x → 
                  case (Lt-Nat.lt-or-eq-biimpl-leq (succ N) x).Σ.snd ((Lt-Nat.lt-biimpl-succ-leq N x).Σ.fst N<x) of λ {
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

    decide-Σ-P : Is-decidable (Σ Nat P)
    decide-Σ-P =
      case (search-descending-from-Nat {P} {decide-p} m) of λ {
        (left (n , (pn , leq-n), _)) → left (n , pn)
      ; (right ¬pn-below-m) → right (λ (n , pn) → ¬pn-below-m n (mub n pn) pn)
      }

    maximize : Σ Nat P → Σ Nat (λ n → P n × Nat-is-upper-bound {P} n)
    maximize (n , pn) =
      case (search-descending-from-Nat {P} {decide-p} m) of λ {
        (left (m' , (pm' , m'≤m), no-value-from-sm'-upto-m-satisfies)) →
          (m' , pm' , (λ m'' pm'' →
            -- goal : m'' ≤ m'
            Lt-Nat.by-comparing m'' m' λ {
              (left (left m''<m')) → Lt-Nat.as-leq m'' m' m''<m'
            ; (left (right refl)) → Leq-Nat.Leq-Nat-refl m''
            ; (right m'<m'') →
              case (no-value-from-sm'-upto-m-satisfies m'' pm'') of λ {
                (left m''≤m') → m''≤m'
              ; (right m<m'') → absurd ((Lt-Nat.lt-biimpl-not-flip-leq m m'').Σ.fst m<m'' (mub m'' pm'')) -- impossible
              }
          }))
      ; (right ¬pm'-below-m) → absurd (¬pm'-below-m n (mub n pn) pn) -- impossible
      }
 