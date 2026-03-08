open import Function.Base using (case_of_)

module _ where
  open import section-11 public

  open Σ-Basic

  open Homotopy
  open Homotopy.Symbolic
  open ≡-Basic
  open ≡-Reasoning

  open Equivalence
  open Equivalence.Symbolic

  open import Agda.Primitive

  -- definition 12.1.1
  Is-prop : {l : Level} → Set l → Set l
  Is-prop {l} A = (x : A) → (y : A) → Is-contr (x ≡ y)

  Props : (l : Level) → Set (lsuc l)
  Props l = Σ-poly (Set l) (λ X → Is-prop X)

  -- example 12.1.2
  is-contr-then-is-prop : {A : Set} → Is-contr A → Is-prop A
  is-contr-then-is-prop contr = is-contr-then-identity-is-contr contr

  Unit-is-prop : Is-prop Unit
  Unit-is-prop = is-contr-then-is-prop Unit-is-contr

  Empty-is-prop : Is-prop Empty
  Empty-is-prop _ ()

  -- proposition 12.1.3
  module Is-prop-characterisation {A : Set} where
    i = Is-prop A
    ii = (x : A) → (y : A) → (x ≡ y)
    iii = A → Is-contr A
    iv = Is-emb (const {A} {Unit} unit)

    i→ii : i → ii
    i→ii is-prop x y = Σ.fst (is-prop x y)

    ii→iii : ii → iii
    ii→iii identify-any x = (x , (λ y → identify-any x y))

    iii→iv : iii → iv
    iii→iv is-contr-if-inhabited =
      let
        conditionally-is-emb-then-is-emb : {X Y : Set} → (f : X → Y) → (X → Is-emb f) → Is-emb f
        conditionally-is-emb-then-is-emb {X} {Y} f conditionally-is-emb = (λ x y → conditionally-is-emb x x y)
      in
        conditionally-is-emb-then-is-emb (const {A} {Unit} unit) (λ (x : A) →
          is-equiv-then-is-emb (
            contr-then-const-unit-is-equiv (
              is-contr-if-inhabited x))
        )

    iv→i : iv → i
    iv→i const-is-emb x y =
      cod-of-equiv-is-contr-then-dom-is-contr (const-is-emb x y) (Unit-is-prop unit unit)

    ii→i : ii → i
    ii→i = iv→i ∘ iii→iv ∘ ii→iii

    i→iii : i → iii
    i→iii = ii→iii ∘ i→ii

    i↔iii : i ↔ iii
    i↔iii = (i→iii , iv→i ∘ iii→iv)

  is-prop-then-any-two-eq : {A : Set} → Is-prop A → (x y : A) → (x ≡ y)
  is-prop-then-any-two-eq is-prop x y =
    Is-prop-characterisation.i→ii is-prop x y

  identity-any-two-in-props : ((P , PProp) : Props _) → (x : P) → (y : P) → (x ≡ y)
  identity-any-two-in-props (P , PProp) = Is-prop-characterisation.i→ii PProp

  -- proposition 12.1.4
  map-between-props-is-equiv-iff-converse : ((P , PProp) (Q , QProp) : Props _) → (map : P → Q) → Is-equiv map ↔ (Q → P)
  map-between-props-is-equiv-iff-converse P Q map =
    (
      (λ equiv → ≃-inverse-map-for equiv) ,
      (λ converse →
        has-inverse-equiv
          ( converse
          , (λ q → identity-any-two-in-props Q _ q)
          , (λ p → identity-any-two-in-props P _ p)))
    )

  props-equiv-iff-iff : ((P , PProp) (Q , QProp) : Props _) → (P ≃ Q) ↔ (P ↔ Q)
  props-equiv-iff-iff P Q =
    (
      (λ { (map , eqv) → (map , Σ.fst (map-between-props-is-equiv-iff-converse P Q map) eqv) }),
      (λ { (forward , backward) → (forward , Σ.snd (map-between-props-is-equiv-iff-converse P Q forward) backward) })
    )

  -- definition 12.2.1
  Is-subtype : {A : Set} → (B : A → Set) → Set
  Is-subtype {A} B = (x : A) → Is-prop (B x)

  -- lemma 12.2.2
  is-prop-pulled-back-by-equiv : {A B : Set} → {f : A → B} → Is-equiv f → Is-prop B → Is-prop A
  is-prop-pulled-back-by-equiv {A} {B} {f} equiv is-prop x y =
    cod-of-equiv-is-contr-then-dom-is-contr
      (is-equiv-then-is-emb equiv x y)
      (is-prop (f x) (f y))

  is-prop-preserved-by-equiv : {A B : Set} → {f : A → B} → Is-equiv f → Is-prop A → Is-prop B
  is-prop-preserved-by-equiv {A} {B} {f} equiv is-prop =
    is-prop-pulled-back-by-equiv (≃-inverse-map-is-equiv equiv) is-prop

  dom-of-equiv-is-prop-iff-cod-is-prop : {A B : Set} → {f : A → B} → Is-equiv f → Is-prop A ↔ Is-prop B
  dom-of-equiv-is-prop-iff-cod-is-prop {A} {B} {f} equiv =
    (is-prop-preserved-by-equiv equiv , is-prop-pulled-back-by-equiv equiv)

  open ↔-Reasoning

  -- theorem 12.2.3
  module _ where
    ap-is-equiv-iff-ap-inverse-is-equiv : {A B : Set} → {f : A → B} → (x y : A) → Is-equiv (ap f {x} {y}) ↔ Is-equiv (λ p → ap f {x} {y} (inverse p))
    ap-is-equiv-iff-ap-inverse-is-equiv x y =
      (
        (λ eqv → comp-equivs-is-equiv eqv EqualityOps.inv-is-equiv)
      , (λ eqv → former-and-comp-are-equivs-then-latter-is-equiv (λ { refl → refl }) EqualityOps.inv-is-equiv eqv)
      )

    -- NOTE: It looks like Lemma 12.2.2 is not involved in the proof.
    is-emb-iff-fibs-are-props : {A B : Set} → {f : A → B} → Is-emb f ↔ ((b : B) → Is-prop (fib f b))
    is-emb-iff-fibs-are-props {A} {B} {f} =
      begin-↔
        Is-emb f                                                            ↔⟨⟩
        ((x : A) → (y : A) → Is-equiv (λ (p : x ≡ y) → ap f p))             ↔⟨ depfn-biimpl-2 (λ x y → ap-is-equiv-iff-ap-inverse-is-equiv x y) ⟩
        ((x : A) → (y : A) → Is-equiv (λ (p : y ≡ x) → ap f (inverse p)))   ↔⟨ flipDependentBiimpl ⟩
        ((y : A) → (x : A) → Is-equiv (λ (p : y ≡ x) → ap f (inverse p)))   ↔⟨ depfn-biimpl (λ y → fundamental-thm-of-identity-types.i-at-fn↔ii (λ x (p : y ≡ x) → ap f (inverse p))) ⟩
        ((y : A) → Is-contr (Σ A (λ x → f x ≡ f y)))                        ↔⟨⟩
        ((y : A) → Is-contr (fib f (f y)))                                  ↔⟨ depfn-biimpl (λ y → ((λ contr b p → tr _ p contr) , (λ contr → contr (f y) refl))) ⟩
        ((y : A) → (b : B) → (p : f y ≡ b) → Is-contr (fib f b))            ↔⟨ flipDependentBiimpl ⟩
        ((b : B) → (y : A) → (p : f y ≡ b) → Is-contr (fib f b))            ↔⟨ depfn-biimpl (λ b → uncurry-biimpl) ⟩
        ((b : B) → fib f b → Is-contr (fib f b))                            ↔⟨← depfn-biimpl (λ b → Is-prop-characterisation.i↔iii) ⟩
        ((b : B) → Is-prop (fib f b))                                       ∎-↔

  -- corollary 12.2.4
  fst-is-emb-iff-is-subtype : {A : Set} → {B : A → Set} → Is-emb (Σ.fst {A} {B}) ↔ Is-subtype B
  fst-is-emb-iff-is-subtype {A} {B} =
    begin-↔
      Is-emb (Σ.fst {A} {B})                           ↔⟨ is-emb-iff-fibs-are-props ⟩
      ((x : A) → Is-prop (fib (Σ.fst {A} {B}) x))      ↔⟨ depfn-biimpl (λ x → dom-of-equiv-is-prop-iff-cod-is-prop (tr-from-fib-pr₁-is-equiv x)) ⟩
      ((x : A) → Is-prop (B x))                        ↔⟨⟩
      Is-subtype B                                     ∎-↔

  subtype-and-fst-eq-then-pair-eq : {A : Set} → {B : A → Set} → Is-subtype B → {p1 p2 : Σ A B} → (Σ.fst p1 ≡ Σ.fst p2) → p1 ≡ p2
  subtype-and-fst-eq-then-pair-eq is-subtype {p1} {p2} =
    ≃-inverse-map-for ((Σ.snd fst-is-emb-iff-is-subtype) is-subtype p1 p2)

  -- definition 12.3.1
  Is-set : (A : Set) → Set
  Is-set A = (x : A) → (y : A) → Is-prop (x ≡ y)

  -- example 12.3.2
  Eq-Nat-is-prop : (n m : Nat) → Is-prop (Eq-Nat n m)
  Eq-Nat-is-prop zero zero         = Unit-is-prop
  Eq-Nat-is-prop zero (succ m)     = Empty-is-prop
  Eq-Nat-is-prop (succ n) zero     = Empty-is-prop
  Eq-Nat-is-prop (succ n) (succ m) = Eq-Nat-is-prop n m

  Nat-is-set : Is-set Nat
  Nat-is-set = λ n m → is-prop-pulled-back-by-equiv (Eq-Nat-refl-is-equiv n m) (Eq-Nat-is-prop n m)

  -- proposition 12.3.3
  axiom-K : Set → Set
  axiom-K A = (x : A) → (p : x ≡ x) → refl-at x ≡ p

  Set-iff-axiom-K : (A : Set) → Is-set A ↔ axiom-K A
  Set-iff-axiom-K A =
    ( (λ is-set x p → Is-prop-characterisation.i→ii (is-set x x) (refl-at x) p)
    , (λ axiom-k x y → Is-prop-characterisation.ii→i (λ p q → ≡-Basic1.con-cancel-right refl p q (axiom-k _ _))))

  -- theorem 12.3.4
  -- NOTE: this theorem would not require the ((x : A) → R x x) parameter
  reflexive-propositional-relation-makes-fam-of-maps-from-identity-types-equivs :
        {A : Set} → (R : A → A → Set) →
        (propositional : (x y : A) → Is-prop (R x y)) →
        (maps-into-identity-types : (x y : A) → R x y → x ≡ y) →
        (fam-of-maps : (x y : A) → (x ≡ y) → R x y) →
        (x y : A) → Is-equiv (fam-of-maps x y)
  reflexive-propositional-relation-makes-fam-of-maps-from-identity-types-equivs
      {A} R propositional maps-into-identity-types fam-of-maps x =
    fundamental-thm-of-identity-types.ii→i-at-fn ΣARx-is-contr (fam-of-maps x)
    where
      f : Σ A (λ y → R x y) → Σ A (λ y → x ≡ y)
      f = totalization (maps-into-identity-types x)

      f-retr : Retr f
      f-retr =
        ( (λ { (a , p) → (a , fam-of-maps x a p) })
        , (λ { (a , _) → subtype-and-fst-eq-then-pair-eq (propositional x) refl }))

      ΣARx-is-contr : Is-contr (Σ A (R x))
      ΣARx-is-contr =
        retract-of-contr-is-contr
          (f , f-retr)
          (identity-with-an-endpoint-fixed-is-contr x)

  underlying-type-of-reflexive-propositional-relation-is-set :
        {A : Set} → (R : A → A → Set) →
        (reflexive : (x : A) → R x x) →
        (propositional : (x y : A) → Is-prop (R x y)) →
        (maps-into-identity-types : (x y : A) → R x y → x ≡ y) →
        Is-set A
  underlying-type-of-reflexive-propositional-relation-is-set
      {A} R reflexive propositional maps-into-identity-types x y =
    is-prop-pulled-back-by-equiv
      (reflexive-propositional-relation-makes-fam-of-maps-from-identity-types-equivs
        R propositional maps-into-identity-types
        (λ { x .x refl → reflexive x })
        x y)
      (propositional x y)

  open EmptyBasic

  -- theorem 12.3.5
  has-decidable-equality-then-is-set : {A : Set} → Has-decidable-eq A → Is-set A
  has-decidable-equality-then-is-set {A} decide-eq =
    underlying-type-of-reflexive-propositional-relation-is-set
      R R-is-reflexive R-applied-is-prop (λ x y → f x y (decide-eq x y))
    where
      R' : (x y : A) → ((x ≡ y) +₀ (x ≢ y)) → Set
      R' x y (left p) = Unit
      R' x y (right ¬p) = Empty

      R : (x y : A) → Set
      R x y = R' x y (decide-eq x y)

      R-applied-is-prop : (x y : A) → Is-prop (R x y)
      R-applied-is-prop x y with decide-eq x y
      ...                      | (left p)      = Unit-is-prop
      ...                      | (right ¬p)    = Empty-is-prop

      R-is-reflexive : (x : A) → R x x
      R-is-reflexive x with decide-eq x x
      ...                 | (left x≡x)    = unit
      ...                 | (right x≢x)   = x≢x refl

      f : (x y : A) → (q : (x ≡ y) +₀ (x ≢ y)) → (R' x y q) → (x ≡ y)
      f x y (left p)   _ = p
      f x y (right ¬p) ()

  data TruncLevel : Set where
    -2-Trunc : TruncLevel
    succ-Trunc : TruncLevel → TruncLevel

  TruncLevel-from-Nat : Nat → TruncLevel
  TruncLevel-from-Nat zero     = succ-Trunc (succ-Trunc -2-Trunc)
  TruncLevel-from-Nat (succ n) = succ-Trunc (TruncLevel-from-Nat n)

  -- definition 12.4.1
  Is-trunc : TruncLevel → {l : Level} → Set l → Set l
  Is-trunc -2-Trunc A = Is-contr A
  Is-trunc (succ-Trunc l) A = (x y : A) → Is-trunc l (x ≡ y)

  Set-Trunc : (l : Level) → (k : TruncLevel) → Set (lsuc l)
  Set-Trunc l k = Σ-poly (Set l) (Is-trunc k)

  Is-trunc-map : (k : TruncLevel) → {A B : Set} → (f : A → B) → Set
  Is-trunc-map k {A} {B} f = (b : B) → Is-trunc k (fib f b)

  -- proposition 12.4.3
  k-type-is-succ-k-type : {A : Set} → {k : TruncLevel} → Is-trunc k A → Is-trunc (succ-Trunc k) A
  k-type-is-succ-k-type {A} { -2-Trunc } A-is-contr = is-contr-then-is-prop A-is-contr
  k-type-is-succ-k-type {A} { (succ-Trunc k) } A-is-sk-trunc x y = k-type-is-succ-k-type (A-is-sk-trunc x y)

  is-contr-then-is-k-type : {A : Set} → {k : TruncLevel} → Is-contr A → Is-trunc k A
  is-contr-then-is-k-type {A} { -2-Trunc } contr = contr
  is-contr-then-is-k-type {A} { (succ-Trunc k) } contr = k-type-is-succ-k-type (is-contr-then-is-k-type contr)

  equiv-then-is-k-trunc-map : {A B : Set} → {k : TruncLevel} → {f : A → B} → Is-equiv f → Is-trunc-map k f
  equiv-then-is-k-trunc-map f-is-equiv b = is-contr-then-is-k-type (is-equiv-then-is-contr-fn f-is-equiv b)

  -- corollary 12.4.4
  identity-type-of-k-type-is-k-type : {A : Set} → {k : TruncLevel} → Is-trunc k A → (x y : A) → Is-trunc k (x ≡ y)
  identity-type-of-k-type-is-k-type {A} {k} = k-type-is-succ-k-type

  -- proposition 12.4.5
  is-k-type-pulled-back-by-equiv : {A B : Set} → {k : TruncLevel} → Is-trunc k B →
                                   {e : A → B} → Is-equiv e → Is-trunc k A
  is-k-type-pulled-back-by-equiv {A} {B} { -2-Trunc } B-is-contr {e} e-eqv =
    cod-of-equiv-is-contr-then-dom-is-contr e-eqv B-is-contr
  is-k-type-pulled-back-by-equiv {A} {B} { (succ-Trunc k) } B-is-sk-trunc {e} e-eqv x y =
    is-k-type-pulled-back-by-equiv (B-is-sk-trunc (e x) (e y)) (is-equiv-then-is-emb e-eqv x y)

  equiv-to-k-type-then-is-k-type : {A B : Set} → {k : TruncLevel} → (A ≃ B) → Is-trunc k A → Is-trunc k B
  equiv-to-k-type-then-is-k-type {A} {B} {k} (e , e-eqv) A-is-k-type =
    is-k-type-pulled-back-by-equiv A-is-k-type (≃-inverse-map-is-equiv e-eqv)

  equiv-then-k-type-iff-k-type : {A B : Set} → (A ≃ B) → {k : TruncLevel} → Is-trunc k A ↔ Is-trunc k B
  equiv-then-k-type-iff-k-type {A} {B} eqv {k} =
    (equiv-to-k-type-then-is-k-type eqv , equiv-to-k-type-then-is-k-type (≃-comm eqv))

  -- corollary 12.4.6
  dom-of-emb-into-succk-type-is-succk-type : {A B : Set} → {f : A → B} → Is-emb f →
                                             {k : TruncLevel} → Is-trunc (succ-Trunc k) B → Is-trunc (succ-Trunc k) A
  dom-of-emb-into-succk-type-is-succk-type {A} {B} {f} f-emb {k} B-is-sk-trunc x y =
    is-k-type-pulled-back-by-equiv (B-is-sk-trunc (f x) (f y)) (f-emb x y)

  open Equivalence-Reasoning
  open EqualityOps

  -- theorem 12.4.7
  map-is-sk-trunc-iff-ap-is-k-trunc : {A B : Set} → {f : A → B} → {k : TruncLevel} →
                                      Is-trunc-map (succ-Trunc k) f ↔ ((x y : A) → Is-trunc-map k (ap f {x} {y}))
  map-is-sk-trunc-iff-ap-is-k-trunc {A} {B} {f} {k} = (forward , backward)
    where
      -- NOTE: the book tries to prove fib-eq-≃-fib-apf-concat on the spot,
      --       but we have in fact shown it in 11.6.3
      backward : ((x y : A) → Is-trunc-map k (ap f)) → Is-trunc-map (succ-Trunc k) f
      backward ap-is-k-trunc b s@(x , p) t@(y , q) =
        equiv-to-k-type-then-is-k-type
          (≃-comm (fib-eq-≃-fib-apf-concat f b s t))
          (ap-is-k-trunc x y (p · q ⁻¹))

      forward-lemma : (b : B) → (x y : A) → (p : f x ≡ f y) →
                      fib (ap f) p ≃ ((x , p) ≡ ((y , refl-at (f y)) typed (fib f (f y))))
      forward-lemma b x y p =
        begin-≃
          fib (ap f) p                      ≃⟨← (_ , tr-is-equiv (fib (ap f)) (·-runit _)) ⟩
          fib (ap f) (p · refl ⁻¹)          ≃⟨← fib-eq-≃-fib-apf-concat f (f y) (x , p) (y , refl) ⟩
          (x , p) ≡ ((y , refl-at (f y)))   ∎-≃

      forward : Is-trunc-map (succ-Trunc k) f → (x y : A) → Is-trunc-map k (ap f)
      forward f-is-sk-trunc x y p =
        equiv-to-k-type-then-is-k-type
          (≃-comm (forward-lemma (f x) x y p))
          (f-is-sk-trunc (f y) (x , p) (y , refl))

  precomp-to-depfn : {X A : Set} → (f : X → A) → {B : A → Set} → ((a : A) → B a) → ((x : X) → B (f x))
  precomp-to-depfn f g x = g (f x)

  unprecomp-split-epi-from-depfn : {B C : Set} → (e : B → C) → Sect e → {P : C → Set} →
                                   ((b : B) → P (e b)) → ((c : C) → P c)
  unprecomp-split-epi-from-depfn {B} {C} e (s , S) {P} t c = tr P (S c) (t (s c))

  postcomp-by-emb-preserves-fibers : {A B C : Set} → (f : A → B) → {m : B → C} → Is-emb m →
                                     (b : B) → fib f b ≃ fib (m ∘ f) (m b)
  postcomp-by-emb-preserves-fibers {A} {B} {C} f {m} m-emb b =
    -- Goal: Σ A (λ a → f a = b) ≃ Σ A (λ a → m (f a) = m b)
    pointwise-equiv-then-tot-equiv (λ a →
      -- Goal: (f a = b) ≃ (m (f a) = m b)
      build-tpe-equiv (m-emb (f a) b))

  postcomp-by-equiv-is-k-trunc-iff-original-is :
        {A B C : Set} → {k : TruncLevel} → (f : A → B) → {e : B → C} → Is-equiv e →
        Is-trunc-map k f ↔ Is-trunc-map k (e ∘ f)
  postcomp-by-equiv-is-k-trunc-iff-original-is {A} {B} {C} {k} f {e} e-eqv@(S , _) =
    begin-↔
      Is-trunc-map k f                            ↔⟨⟩
      ((b : B) → Is-trunc k (fib f b))            ↔⟨ depfn-biimpl (λ b → equiv-then-k-type-iff-k-type
                                                       (postcomp-by-emb-preserves-fibers f (is-equiv-then-is-emb e-eqv) b)) ⟩
      ((b : B) → Is-trunc k (fib (e ∘ f) (e b)))  ↔⟨← (precomp-to-depfn e , unprecomp-split-epi-from-depfn e S) ⟩
      ((c : C) → Is-trunc k (fib (e ∘ f) c))      ↔⟨⟩
      Is-trunc-map k (e ∘ f)                      ∎-↔

  -- exercise 12.1
  Bool-is-set : Is-set Bool
  Bool-is-set =
    underlying-type-of-reflexive-propositional-relation-is-set
      Eq-Bool
      Eq-Bool.Eq-Bool-refl
      (λ { false false → Unit-is-prop
         ; false true  → Empty-is-prop
         ; true false  → Empty-is-prop
         ; true true   → Unit-is-prop })
      (λ x y → Σ.snd (Eq-Bool.Bool-≡-iff-Eq-Bool x y))

  Bool-is-set-by-decEq : Is-set Bool
  Bool-is-set-by-decEq = has-decidable-equality-then-is-set Bool-has-decidable-eq
    where
      Bool-has-decidable-eq : Has-decidable-eq Bool
      Bool-has-decidable-eq false false = left refl
      Bool-has-decidable-eq false true = right (λ ())
      Bool-has-decidable-eq true false = right (λ ())
      Bool-has-decidable-eq true true = left refl

  -- exercise 12.6 (will be useful in 12.2)
  module _ where
    conditionally-sk-type-then-is-sk-type : {A : Set} → {k : TruncLevel} → (A → Is-trunc (succ-Trunc k) A) → Is-trunc (succ-Trunc k) A
    conditionally-sk-type-then-is-sk-type {A} {k} conditionally-sk-trunc x y = conditionally-sk-trunc x x y

    -- exercise 12.6.a
    family-is-k-trunc-iff-tot-is-k-trunc : {A : Set} → {k : TruncLevel} → Is-trunc k A →
                                           {B : A → Set} → ((x : A) → Is-trunc k (B x)) ↔ Is-trunc k (Σ A B)
    family-is-k-trunc-iff-tot-is-k-trunc {A} { -2-Trunc } a-is-contr@(ca , _) {B} =
      begin-↔
        ((x : A) → Is-trunc -2-Trunc (B x))   ↔⟨⟩
        ((x : A) → Is-contr (B x))            ↔⟨ depfn-biimpl (λ x →
                                                    equiv-then-contr-iff-contr (
                                                      ≃-comm (Σ-≃-sections-at-base-center
                                                        (x , recenter-contraction-at x a-is-contr)))) ⟩
        ((x : A) → Is-contr (Σ A B))          ↔⟨ (ev-pt ca , const) ⟩
        Is-contr (Σ A B)                      ↔⟨⟩
        Is-trunc -2-Trunc (Σ A B)             ∎-↔
    family-is-k-trunc-iff-tot-is-k-trunc {A} { succ-Trunc k } a-is-sk-trunc {B} =
      begin-↔
        ((x : A) → Is-trunc (succ-Trunc k) (B x))                                                  ↔⟨⟩
        ((x : A) → (bx bx' : B x) → Is-trunc k (bx ≡ bx'))                                         ↔⟨ rel-on-fiber-biimpl-rel-on-a-transported-fiber ⟩
        ((x : A) → (bx : B x) → (y : A) → (by : B y) → (α : x ≡ y) → Is-trunc k (tr B α bx ≡ by))  ↔⟨ uncurry-biimpl ⟩
        (((x , bx) : Σ A B) → (y : A) → (by : B y) → (α : x ≡ y) → Is-trunc k (tr B α bx ≡ by))    ↔⟨ depfn-biimpl (λ s → uncurry-biimpl) ⟩
        (((x , bx) (y , by) : Σ A B) → (α : x ≡ y) → Is-trunc k (tr B α bx ≡ by))                  ↔⟨ depfn-biimpl-2 (λ { (x , bx) (y , by) → family-is-k-trunc-iff-tot-is-k-trunc (a-is-sk-trunc x y)}) ⟩
        (((x , bx) (y , by) : Σ A B) → Is-trunc k (Σ (x ≡ y) (λ α → tr B α bx ≡ by)))              ↔⟨⟩
        (((x , bx) (y , by) : Σ A B) → Is-trunc k (Eq-Σ (x , bx) (y , by)))                        ↔⟨ depfn-biimpl-2 (λ s t → equiv-then-k-type-iff-k-type (≃-comm pair-eq-≃-Eq-Σ)) ⟩
        (((x , bx) (y , by) : Σ A B) → Is-trunc k ((x , bx) ≡ (y , by)))                           ↔⟨ depfn-biimpl-2 (λ { (x , bx) (y , by) → (id , id) }) ⟩
        ((s t : Σ A B) → Is-trunc k (s ≡ t))                                                       ↔⟨⟩
        Is-trunc (succ-Trunc k) (Σ A B)                                                            ∎-↔
      where
        rel-on-fiber-biimpl-rel-on-a-transported-fiber :
              {A : Set} → {B : A → Set} → {C : (x : A) → B x → B x → Set} →
              ((x : A) → (bx bx' : B x) → C x bx bx') ↔ ((x : A) → (bx : B x) → (y : A) → (by : B y) → (p : x ≡ y) → C y (tr B p bx) by)
        rel-on-fiber-biimpl-rel-on-a-transported-fiber {A} {B} {C} =
          ((λ { lhs x bx .x bx' refl → lhs x bx bx' }) , (λ { rhs x bx bx' → rhs x bx x bx' refl }))

    -- exercise 12.6.b
    map-to-k-type-is-k-trunc-iff-dom-is-k-trunc :
          {A B : Set} → {k : TruncLevel} → Is-trunc k B →
          {f : A → B} → Is-trunc-map k f ↔ Is-trunc k A
    map-to-k-type-is-k-trunc-iff-dom-is-k-trunc {A} {B} {k} B-is-k-trunc {f} =
      begin-↔
        Is-trunc-map k f                   ↔⟨⟩
        ((b : B) → Is-trunc k (fib f b))   ↔⟨ family-is-k-trunc-iff-tot-is-k-trunc B-is-k-trunc ⟩
        Is-trunc k (Σ B (fib f))           ↔⟨ equiv-then-k-type-iff-k-type (≃-comm (fiber-decomposition f)) ⟩
        Is-trunc k A                       ∎-↔

  prod-of-k-types-is-k-type : {A B : Set} → {k : TruncLevel} → Is-trunc k A → Is-trunc k B → Is-trunc k (A × B)
  prod-of-k-types-is-k-type {A} {B} {k} A-is-k-trunc B-is-k-trunc =
    Σ.fst (family-is-k-trunc-iff-tot-is-k-trunc A-is-k-trunc) (λ x → B-is-k-trunc)

  product-of-props-is-prop : {A B : Set} → Is-prop A → Is-prop B → Is-prop (A × B)
  product-of-props-is-prop = prod-of-k-types-is-k-type

  -- exercise 12.2
  underlying-type-of-reflexive-antisymmetric-rel-is-set : {A : Set} → (R : A → A → Set) →
        (R-is-prop : (x y : A) → Is-prop (R x y)) →
        (reflexive : (x : A) → R x x) →
        (antisymmetric : (x y : A) → R x y → R y x → x ≡ y) →
        Is-set A
  underlying-type-of-reflexive-antisymmetric-rel-is-set {A} R R-is-prop reflexive antisymmetric =
    underlying-type-of-reflexive-propositional-relation-is-set
      R'
      (λ x → (reflexive x , reflexive x))
      (λ x y → product-of-props-is-prop (R-is-prop x y) (R-is-prop y x))
      (λ { x y (Rxy , Ryx) → antisymmetric x y Rxy Ryx })
    where
      R' : (x y : A) → Set
      R' x y = R x y × R y x

  -- exercise 12.3
  module _ where
    is-emb-then-is-inj : {A B : Set} → {f : A → B} → Is-emb f → Is-inj f
    is-emb-then-is-inj {A} {B} {f} emb x y p = ≃-inverse-map-for (emb x y) p

    -- exercise 12.3.a
    inj-to-a-set-is-emb : {A B : Set} → Is-set B → {f : A → B} → Is-inj f → Is-emb f
    inj-to-a-set-is-emb {A} {B} B-is-set {f} inj x y =
      has-inverse-equiv
        ( (λ fx≡fy → (inj x x refl) ⁻¹ · inj x y fx≡fy)
        , (λ fx≡fy → is-prop-then-any-two-eq (B-is-set (f x) (f y)) _ _)
        , (λ { refl → ·-linv (inj x x refl) }))

    dom-of-inj-to-a-set-is-set : {A B : Set} → Is-set B → {f : A → B} → Is-inj f → Is-set A
    dom-of-inj-to-a-set-is-set {A} {B} B-is-set {f} inj =
      dom-of-emb-into-succk-type-is-succk-type (inj-to-a-set-is-emb B-is-set inj) B-is-set

    open NatBasic.Symbolic
    open Nat-EqualityThroughEq-Nat
    -- exercise 12.3.b
    add-nat-left-is-emb : (m : Nat) → Is-emb (λ n → m + n)
    add-nat-left-is-emb m = inj-to-a-set-is-emb Nat-is-set (λ n1 n2 → Σ.snd (add-inj-left n1 n2 m))

    open Leq-Nat
    open Leq-Nat.Symbolic

    Leq-Nat-is-prop : (m n : Nat) → Is-prop (m ≤ n)
    Leq-Nat-is-prop zero y = Unit-is-prop
    Leq-Nat-is-prop (succ x) zero = Empty-is-prop
    Leq-Nat-is-prop (succ x) (succ y) = Leq-Nat-is-prop x y

    set-elem-having-preimage-under-inj-is-prop : {A B : Set} → Is-set A → {f : B → A} → Is-inj f →
                                                 (x : A) → Is-prop (Σ B (λ b → f b ≡ x))
    set-elem-having-preimage-under-inj-is-prop {A} {B} A-is-set {f} inj x =
      Is-prop-characterisation.ii→i (λ { (b1 , p) (b2 , q) →
        subtype-and-fst-eq-then-pair-eq (λ b → A-is-set (f b) x) (inj b1 b2 (p · q ⁻¹))
      })

    exists-diff-to-nat-is-prop : (m n : Nat) → Is-prop (Σ Nat (λ k → m + k ≡ n))
    exists-diff-to-nat-is-prop m n =
      set-elem-having-preimage-under-inj-is-prop
        Nat-is-set
        (is-emb-then-is-inj (add-nat-left-is-emb m))
        n

    Leq-Nat-equiv-exists-diff : (m n : Nat) → (m ≤ n) ≃ (Σ Nat (λ k → m + k ≡ n))
    Leq-Nat-equiv-exists-diff m n =
      Σ.snd
        (props-equiv-iff-iff
          (m ≤ n , Leq-Nat-is-prop m n)
          (Σ Nat (λ k → m + k ≡ n) , exists-diff-to-nat-is-prop m n))
        (leq-iff-exists-diff m n)

    -- exercise 12.3.c
    succ-mul-is-emb : (m : Nat) → Is-emb (λ n → (succ m) * n)
    succ-mul-is-emb m = inj-to-a-set-is-emb Nat-is-set (λ n1 n2 → Σ.snd (mul-inj-left n1 n2 m))

    open DivisibilityBasic.Symbolic
    divisibility-is-prop : (d n : Nat) → Is-prop (succ d ∣ n)
    divisibility-is-prop d n =
      set-elem-having-preimage-under-inj-is-prop
        Nat-is-set
        (is-emb-then-is-inj (succ-mul-is-emb d))
        n

  -- exercise 12.4
  module _ where
    copr-of-inhabited-is-not-prop : {A B : Set} → (a : A) → (b : B) → ¬ Is-prop (A +₀ B)
    copr-of-inhabited-is-not-prop a b is-prop =
      let (left-right-neq , _) = left-right-eq-equiv-empty _ _
      in left-right-neq (Is-prop-characterisation.i→ii is-prop (left a) (right b))

    -- exercise 12.4.a
    copr-of-contr-types-is-not-contr : {A B : Set} → Is-contr A → Is-contr B → ¬ Is-contr (A +₀ B)
    copr-of-contr-types-is-not-contr (a , _) (b , _) is-contr =
      copr-of-inhabited-is-not-prop a b (k-type-is-succ-k-type is-contr)

    _⊕₀_ : Set → Set → Set
    P ⊕₀ Q = (P × (¬ Q)) +₀ (Q × (¬ P))
    infixl 30 _⊕₀_

    -- exercise 12.4.b
    is-contr-prop-copr-iff-xdisj : {P Q : Set} → Is-prop P → Is-prop Q → Is-contr (P +₀ Q) ↔ (P ⊕₀ Q)
    is-contr-prop-copr-iff-xdisj {P} {Q} P-is-prop Q-is-prop =
      (forward , backward)
      where
        forward : Is-contr (P +₀ Q) → (P ⊕₀ Q)
        forward contrPQ@((left p) , contr-to-lp) =
          left (p , λ q →
            copr-of-contr-types-is-not-contr
              (Is-prop-characterisation.i→iii P-is-prop p)
              (Is-prop-characterisation.i→iii Q-is-prop q)
              contrPQ
          )
        forward contrPQ@((right q) , contr-to-rq) =
          right (q , λ p →
            copr-of-contr-types-is-not-contr
              (Is-prop-characterisation.i→iii P-is-prop p)
              (Is-prop-characterisation.i→iii Q-is-prop q)
              contrPQ
          )

        backward : (P ⊕₀ Q) → Is-contr (P +₀ Q)
        backward (left (p , nq)) =
          is-contr-preserved-by-equiv
            (Σ.snd (left-is-equiv-iff-right-type-is-empty P Q) nq)
            (Is-prop-characterisation.i→iii P-is-prop p)
        backward (right (q , np)) =
          is-contr-preserved-by-equiv
            (Σ.snd (right-is-equiv-iff-left-type-is-empty P Q) np)
            (Is-prop-characterisation.i→iii Q-is-prop q)

    -- exercise 12.4.c
    copr-of-props-is-prop-iff-one-implies-neg-of-other : {P Q : Set} → Is-prop P → Is-prop Q →
                                                         Is-prop (P +₀ Q) ↔ (P → ¬ Q)
    copr-of-props-is-prop-iff-one-implies-neg-of-other {P} {Q} P-is-prop Q-is-prop =
      ( (λ prP+Q p q → copr-of-inhabited-is-not-prop p q prP+Q)
      , (λ p-then-nq → Is-prop-characterisation.ii→i (λ where
          (left p) (left p') → ap left (Is-prop-characterisation.i→ii P-is-prop p p')
          (left p) (right q) → absurd (p-then-nq p q)
          (right q) (left p) → absurd (p-then-nq p q)
          (right q) (right q') → ap right (Is-prop-characterisation.i→ii Q-is-prop q q')
      )))

    -- exercise 12.4.d
    copr-of-ssk-types-is-ssk-type : {A B : Set} → {k : TruncLevel} →
          Is-trunc (succ-Trunc (succ-Trunc k)) A → Is-trunc (succ-Trunc (succ-Trunc k)) B →
          Is-trunc (succ-Trunc (succ-Trunc k)) (A +₀ B)
    copr-of-ssk-types-is-ssk-type {A} {B} {k} A-is-ssk B-is-ssk = indunction-on-copr
      where
        indunction-on-copr : Is-trunc (succ-Trunc (succ-Trunc k)) (A +₀ B)
        indunction-on-copr (left a) (left a') p q =
          let
            α : (left {A} {B} a ≡ left a') ≃ (a ≡ a')
            α = ≃-inverse (build-tpe-equiv (left-is-emb A B a a'))
            (f , f-is-equiv) = α
            fp≡fq-is-k-type : Is-trunc k (f p ≡ f q)
            fp≡fq-is-k-type = A-is-ssk a a' (f p) (f q)
            fp≡fq-≃-p≡q : (f p ≡ f q) ≃ (p ≡ q)
            fp≡fq-≃-p≡q = ≃-inverse (build-tpe-equiv (is-equiv-then-is-emb f-is-equiv p q))
          in equiv-to-k-type-then-is-k-type fp≡fq-≃-p≡q fp≡fq-is-k-type
        indunction-on-copr (right b) (right b') p q =
          let
            β : (right {A} {B} b ≡ right b') ≃ (b ≡ b')
            β = ≃-inverse (build-tpe-equiv (right-is-emb A B b b'))
            (g , g-is-equiv) = β
            gp≡gq-is-k-type : Is-trunc k (g p ≡ g q)
            gp≡gq-is-k-type = B-is-ssk b b' (g p) (g q)
            gp≡gq-≃-p≡q : (g p ≡ g q) ≃ (p ≡ q)
            gp≡gq-≃-p≡q = ≃-inverse (build-tpe-equiv (is-equiv-then-is-emb g-is-equiv p q))
          in equiv-to-k-type-then-is-k-type gp≡gq-≃-p≡q gp≡gq-is-k-type
        indunction-on-copr (left a) (right b) p = absurd (Σ.fst (left-right-eq-equiv-empty a b) p)
        indunction-on-copr (right b) (left a) p = absurd (Σ.fst (right-left-eq-equiv-empty a b) p)

    Int-is-set : Is-set Int
    Int-is-set =
      copr-of-ssk-types-is-ssk-type Nat-is-set (
        copr-of-ssk-types-is-ssk-type
          (k-type-is-succ-k-type (k-type-is-succ-k-type Unit-is-contr))
          Nat-is-set)

  -- exercise 12.5
  module _ where
    δ : {A : Set} → A → A × A
    δ {A} a = (a , a)

    -- exercise 12.5.a
    diagonal-is-equiv-iff-is-prop : {A : Set} → Is-equiv (δ {A}) ↔ Is-prop A
    diagonal-is-equiv-iff-is-prop {A} =
      ((λ eqv -> Is-prop-characterisation.ii→i (equiv-then-any-two-eq eqv)) , backward)
      where
        equiv-then-any-two-eq : Is-equiv (δ {A}) → (x y : A) → x ≡ y
        equiv-then-any-two-eq ((s , S) , _) x y with (ap Σ.fst (S (x , y)) , ap Σ.snd (S (x , y)))
        ...                                      | (sxy≡x , sxy≡y) = (sxy≡x) ⁻¹ · (sxy≡y)

        backward : Is-prop A → Is-equiv (δ {A})
        backward A-is-prop =
          has-inverse-equiv
            ( Σ.fst
            , (λ { (x , y) -> is-prop-then-any-two-eq (product-of-props-is-prop A-is-prop A-is-prop) (x , x) (x , y) })
            , (λ x → refl))

    -- exercise 12.5.b
    fib-δ-equiv-≡ : {A : Set} → (x y : A) → fib (δ {A}) (x , y) ≃ (x ≡ y)
    fib-δ-equiv-≡ {A} x y =
      build-tpe-equiv (has-inverse-equiv (backward , (λ { refl → refl }) , backward∘forward~id))
      where
        forward-on-fib-snd : {a : A} → {t : A × A} → (δ a ≡ t) → (Σ.fst t ≡ Σ.snd t)
        forward-on-fib-snd p = (ap Σ.fst p) ⁻¹ · (ap Σ.snd p)

        backward-at : (t : A × A) → (Σ.fst t ≡ Σ.snd t) → fib (δ {A}) t
        backward-at (u , v) p = (u , ap (λ r → (u , r)) p)

        backward : {x y : A} → (x ≡ y) → fib (δ {A}) (x , y)
        backward {x} {y} p = backward-at (x , y) p

        right-inverse' : (a : A) → {t : A × A} → (q : δ a ≡ t) →
              backward-at t (forward-on-fib-snd q) ≡ (a , q)
        right-inverse' a refl = refl

        backward∘forward~id : (z@(a , q) : fib (δ {A}) (x , y)) → backward (forward-on-fib-snd q) ≡ z
        backward∘forward~id (a , q) = right-inverse' a q

  -- exercise 12.7
  module _ where
    -- exercise 12.7.i→ii
    other-inhabited-then-trunc-then-prod-is-trunc : {A B : Set} → {k : TruncLevel} →
          (f : B → Is-trunc (succ-Trunc k) A) →
          (g : A → Is-trunc (succ-Trunc k) B) →
          Is-trunc (succ-Trunc k) (A × B)
    other-inhabited-then-trunc-then-prod-is-trunc {A} {B} {k} f g x@(a1 , b1) y =
      prod-of-k-types-is-k-type (f b1) (g a1) x y

    -- exercise 12.7.ii→i (first half)
    prod-is-trunc-then-linhabited-then-rtrunc : {A B : Set} → {k : TruncLevel} →
          Is-trunc (succ-Trunc k) (A × B) → (a : A) → Is-trunc (succ-Trunc k) B
    prod-is-trunc-then-linhabited-then-rtrunc {A} {B} { -2-Trunc } AB-is-prop a x y =
      let (ax≡ay , contraction) = AB-is-prop (a , x) (a , y)
      in (ap Σ.snd ax≡ay , λ { refl → ap (ap Σ.snd) (contraction refl) })
    prod-is-trunc-then-linhabited-then-rtrunc {A} {B} { succ-Trunc k } AB-is-sk-trunc a x y =
      let trunc-ax≡ay = AB-is-sk-trunc (a , x) (a , y)
          trunc-a≡a-×-x≡y = equiv-to-k-type-then-is-k-type prod-eq-≃-eq-prod trunc-ax≡ay
      in prod-is-trunc-then-linhabited-then-rtrunc {k = k} trunc-a≡a-×-x≡y refl

    prod-is-trunc-then-rinhabited-then-ltrunc : {A B : Set} → {k : TruncLevel} →
          Is-trunc (succ-Trunc k) (A × B) → (b : B) → Is-trunc (succ-Trunc k) A
    prod-is-trunc-then-rinhabited-then-ltrunc {A} {B} { -2-Trunc } AB-is-prop b x y =
      let (bx≡by , contraction) = AB-is-prop (x , b) (y , b)
      in (ap Σ.fst bx≡by , λ { refl → ap (ap Σ.fst) (contraction refl) })
    prod-is-trunc-then-rinhabited-then-ltrunc {A} {B} { succ-Trunc k } AB-is-sk-trunc b x y =
      let trunc-bx≡by = AB-is-sk-trunc (x , b) (y , b)
          trunc-x≡y-×-b≡b = equiv-to-k-type-then-is-k-type prod-eq-≃-eq-prod trunc-bx≡by
      in prod-is-trunc-then-rinhabited-then-ltrunc {k = k} trunc-x≡y-×-b≡b refl

    other-inhabited-then-trunc-iff-prod-is-trunc : {A B : Set} → {k : TruncLevel} →
          ((B → Is-trunc (succ-Trunc k) A) × (A → Is-trunc (succ-Trunc k) B)) ↔ Is-trunc (succ-Trunc k) (A × B)
    other-inhabited-then-trunc-iff-prod-is-trunc {A} {B} {k} =
      ( (λ { (f , g) → other-inhabited-then-trunc-then-prod-is-trunc f g })
      , (λ AB-is-sk-trunc →
        ( prod-is-trunc-then-rinhabited-then-ltrunc AB-is-sk-trunc
        , prod-is-trunc-then-linhabited-then-rtrunc AB-is-sk-trunc)))

    inhabited-then-trunc-iff-prod-is-trunc : {A B : Set} → {k : TruncLevel} →
          (a : A) → (b : B) → (Is-trunc k A × Is-trunc k B) ↔ Is-trunc k (A × B)
    inhabited-then-trunc-iff-prod-is-trunc {A} {B} { -2-Trunc } _ _ =
      (uncurry both-contr-then-product-is-contr , product-is-contr-then-both-contr)
    inhabited-then-trunc-iff-prod-is-trunc {A} {B} { succ-Trunc k } a b =
      trans-biimpl
        ((λ { (trA , trB) → (const trA , const trB) }) , (λ { (f , g) → (f b , g a) }))
        other-inhabited-then-trunc-iff-prod-is-trunc

  -- exercise 12.8
  module _ where
    identity-rw-lr : {A : Set} →
                     {x x' y y' : A} → (l : x ≡ x') → (r : y ≡ y') →
                     (x ≡ y) → (x' ≡ y')
    identity-rw-lr refl refl = id

    identity-rw-lr-is-equiv : {A : Set} → {x x' y y' : A} → (l : x ≡ x') → (r : y ≡ y') →
                              Is-equiv (identity-rw-lr l r)
    identity-rw-lr-is-equiv refl refl = id-is-equiv

    identity-rw-lr-refl-refl : {A : Set} → {x z : A} → (l : x ≡ z) →
                               identity-rw-lr l l refl ≡ refl
    identity-rw-lr-refl-refl refl = refl

    -- exercise 12.8.a
    identity-is-retract-of-section-transported : {A B : Set} → {i : A → B} → {r : B → A} →
                                                 (H : Is-sect-of r i) → (x y : A) →
                                                 Is-retract-of (i x ≡ i y) (x ≡ y)
    identity-is-retract-of-section-transported {A} {B} {i} {r} H x y =
      ( ap i
      , (λ p → identity-rw-lr (H x) (H y) (ap r p))
      , λ { refl → identity-rw-lr-refl-refl (H x) })

    -- exercise 12.8.b
    retract-of-k-type-is-k-type : {A B : Set} → {k : TruncLevel} → Is-trunc k B →
                                  Is-retract-of B A → Is-trunc k A
    retract-of-k-type-is-k-type {A} {B} { -2-Trunc } B-is-contr (_ , retr) =
      retraction-preserves-contr retr B-is-contr
    retract-of-k-type-is-k-type {A} {B} { succ-Trunc k } B-is-sk-trunc (i , r , ri~id) x y =
      retract-of-k-type-is-k-type
        (B-is-sk-trunc (i x) (i y))
        (identity-is-retract-of-section-transported {r = r} ri~id x y)

  -- exercise 12.9
  module _ where
    open ≡-Basic1
    open Has-decidable-eq
    open List-Basic renaming (concat to concat-lst)
    open HomotopyGroupoidSymbolic

    tuple-++ : {A : Set} → (List A × List A) → List A
    tuple-++ {A} (xs , ys) = concat-lst xs ys

    is-decidable-preserved-by-equiv : {A B : Set} → (A ≃ B) → Is-decidable A → Is-decidable B
    is-decidable-preserved-by-equiv {A} {B} (e , _) (left a) = left (e a)
    is-decidable-preserved-by-equiv {A} {B} (e , e-is-eqv) (right na) =
      let e⁻¹ = ≃-inverse-map-for e-is-eqv in right (λ b → na (e⁻¹ b))

    open Lt-Nat
    open Lt-Nat.Symbolic

    list-take : {A : Set} → (n : Nat) → List A → List A
    list-take {A} zero _ = nil
    list-take {A} (succ n) nil = nil
    list-take {A} (succ n) (cons x xs) = cons x (list-take n xs)

    list-drop : {A : Set} → (n : Nat) → List A → List A
    list-drop {A} zero xs = xs
    list-drop {A} (succ n) nil = nil
    list-drop {A} (succ n) (cons x xs) = list-drop n xs

    Is-split-point-pair : {A : Set} → (List A × Nat) → Set
    Is-split-point-pair {A} (lst , idx) = idx < succ (length lst)

    Lt-Nat-is-prop : (n m : Nat) → Is-prop (n < m)
    Lt-Nat-is-prop zero zero = Empty-is-prop
    Lt-Nat-is-prop zero (succ m) = Unit-is-prop
    Lt-Nat-is-prop (succ n) zero = Empty-is-prop
    Lt-Nat-is-prop (succ n) (succ m) = Lt-Nat-is-prop n m

    Is-split-point-pair-is-subtype : {A : Set} → Is-subtype (Is-split-point-pair {A})
    Is-split-point-pair-is-subtype {A} (lst , idx) = Lt-Nat-is-prop idx (succ (length lst))

    List-with-split-point : Set → Set
    List-with-split-point A = Σ (List A × Nat) Is-split-point-pair

    fst-len-<-slen-++ : {A : Set} → (xs ys : List A) → length xs < succ (length (tuple-++ (xs , ys)))
    fst-len-<-slen-++ nil ys = zero-lt-succ (length ys)
    fst-len-<-slen-++ (cons x xs) ys =
      fst-len-<-slen-++ xs ys -- : length xs < succ (length (tuple-++ (xs , ys)))
                              -- = succ (length xs) < succ (succ (length (tuple-++ (xs , ys))))
                              -- = length (cons x xs) < succ (length (cons x (tuple-++ (xs , ys))))
                              -- = length (cons x xs) < succ (length (tuple-++ ((cons x xs) , ys)))

    ++-×-lenfst : {A : Set} → (List A × List A) → List-with-split-point A
    ++-×-lenfst xsys@(xs , ys) = ((tuple-++ xsys , length xs) , fst-len-<-slen-++ xs ys)

    -- "splitting at the split point" is (obviously) the inverse map of ++-×-lenfst
    ++-×-lenfst-is-eqv : {A : Set} → Is-equiv (++-×-lenfst {A})
    ++-×-lenfst-is-eqv {A} =
      has-inverse-equiv
        ( split
        , ++-×-lenfst∘split~id
        , split∘++-×-lenfst~id)
      where
        split-at : {A : Set} → Nat → List A → (List A × List A)
        split-at n xs = (list-take n xs , list-drop n xs)

        split : {A : Set} → List-with-split-point A → (List A × List A)
        split ((lst , idx) , _) = split-at idx lst

        length-take-spp : {A : Set} → (lst : List A) → (idx : Nat) → Is-split-point-pair (lst , idx) →
                          length (list-take idx lst) ≡ idx
        length-take-spp lst zero _ = refl
        length-take-spp nil (succ n) n<0 = absurd (not-lt-zero n n<0)
        length-take-spp (cons x xs) (succ n) sn<slxs = ap succ (length-take-spp xs n sn<slxs)

        ++-split-at-eq : {A : Set} → (n : Nat) → (xs : List A) → tuple-++ (split-at n xs) ≡ xs
        ++-split-at-eq zero xs = refl
        ++-split-at-eq (succ n) nil = refl
        ++-split-at-eq (succ n) (cons x xs) =
          begin
            tuple-++ (split-at (succ n) (cons x xs))                                      ≡⟨⟩
            tuple-++ (list-take (succ n) (cons x xs) , list-drop (succ n) (cons x xs))    ≡⟨⟩
            tuple-++ (cons x (list-take n xs) , list-drop n xs)                           ≡⟨⟩
            cons x (tuple-++ (list-take n xs , list-drop n xs))                           ≡⟨⟩
            cons x (tuple-++ (split-at n xs))                                             ≡⟨ ap (cons x) (++-split-at-eq n xs) ⟩
            cons x xs                                                                     ∎

        ++-×-lenfst∘split~id : {A : Set} → (l : List-with-split-point A) → ++-×-lenfst (split l) ≡ l
        ++-×-lenfst∘split~id {A} ((lst , idx) , is-spp) =
          subtype-and-fst-eq-then-pair-eq Is-split-point-pair-is-subtype
            ( begin
                Σ.fst (++-×-lenfst (split ((lst , idx) , is-spp)))                ≡⟨⟩
                Σ.fst (++-×-lenfst (split-at idx lst))                            ≡⟨⟩
                (tuple-++ (split-at idx lst) , length (list-take idx lst))        ≡⟨ ap2 pair
                                                                                         (++-split-at-eq idx lst)
                                                                                         (length-take-spp lst idx is-spp) ⟩
                (lst , idx)                                                       ≡⟨⟩
                Σ.fst (((lst , idx) , is-spp) typed (List-with-split-point A))    ∎)

        take-concat-eq : {A : Set} → (xs ys : List A) → list-take (length xs) (tuple-++ (xs , ys)) ≡ xs
        take-concat-eq nil ys = refl
        take-concat-eq (cons x xs) ys =
          begin
            list-take (length (cons x xs)) (tuple-++ (cons x xs , ys))    ≡⟨⟩
            list-take (succ (length xs)) (cons x (tuple-++ (xs , ys)))    ≡⟨⟩
            cons x (list-take (length xs) (tuple-++ (xs , ys)))           ≡⟨ ap (cons x) (take-concat-eq xs ys) ⟩
            cons x xs                                                     ∎

        drop-concat-eq : {A : Set} → (xs ys : List A) → list-drop (length xs) (tuple-++ (xs , ys)) ≡ ys
        drop-concat-eq nil ys = refl
        drop-concat-eq (cons x xs) ys =
          begin
            list-drop (length (cons x xs)) (tuple-++ (cons x xs , ys))    ≡⟨⟩
            list-drop (succ (length xs)) (cons x (tuple-++ (xs , ys)))    ≡⟨⟩
            list-drop (length xs) (tuple-++ (xs , ys))                    ≡⟨ drop-concat-eq xs ys ⟩
            ys                                                            ∎

        split∘++-×-lenfst~id : {A : Set} → (xsys : List A × List A) → split (++-×-lenfst xsys) ≡ xsys
        split∘++-×-lenfst~id (xs , ys) = ap2 pair (take-concat-eq xs ys) (drop-concat-eq xs ys)

    fib-tuple-++-has-deceq : {A : Set} → (zs : List A) → Has-decidable-eq (fib tuple-++ zs)
    fib-tuple-++-has-deceq {A} zs (xs1ys1@(xs1 , ys1) , p1) (xs2ys2@(xs2 , ys2) , p2) =
      is-decidable-preserved-by-equiv
        (≃-inverse (fib-identity-equiv-to-eq-fib tuple-++))
        eq-fib-++-is-decidable
      where
        eq-fib-++-is-decidable : Is-decidable (Σ (xs1ys1 ≡ xs2ys2) (λ α → p1 ≡ (ap tuple-++ α) · p2))
        eq-fib-++-is-decidable
          with (Nat-has-decidable-eq (length xs1) (length xs2))
        ... | left len-xs1≡len-xs2  =
                let ++-×-lenfst-eq : ++-×-lenfst xs1ys1 ≡ ++-×-lenfst xs2ys2
                    ++-×-lenfst-eq = eq-pair _ _ ( ap2 pair (p1 · p2 ⁻¹) len-xs1≡len-xs2
                                                 , is-prop-then-any-two-eq (Lt-Nat-is-prop (length xs2) _) _ _)

                    ((ap-++-×-lenfst-sect , S) , _) = ++-×-lenfst-is-emb xs1ys1 xs2ys2

                    α : xs1ys1 ≡ xs2ys2
                    α = ap-++-×-lenfst-sect ++-×-lenfst-eq

                    compute-ap-++-×-lenfst-α : (ap ++-×-lenfst) α ≡ ++-×-lenfst-eq
                    compute-ap-++-×-lenfst-α = S ++-×-lenfst-eq

                    compute-ap-++-α : ap tuple-++ α ≡ p1 · p2 ⁻¹
                    compute-ap-++-α =
                      begin
                        ap tuple-++ α                                     ≡⟨ ap-tuple-++-vs-ap-fst-ap-fst α ⟩
                        ap Σ.fst (ap Σ.fst (ap ++-×-lenfst α))            ≡⟨ ap (ap Σ.fst) (ap (ap Σ.fst) compute-ap-++-×-lenfst-α) ⟩
                        ap Σ.fst (ap Σ.fst ++-×-lenfst-eq)                ≡⟨ ap (ap Σ.fst) (ap-fst-eq-pair _) ⟩
                        ap Σ.fst (ap2 pair (p1 · p2 ⁻¹) len-xs1≡len-xs2)  ≡⟨ ap-fst-ap2-pair (p1 · p2 ⁻¹) len-xs1≡len-xs2 ⟩
                        p1 · p2 ⁻¹                                        ∎
                in left (α , (con-cancel-right _ _ _ compute-ap-++-α) ⁻¹)
                where
                  opaque
                    -- Agda seems to reduce (++-×-lenfst-is-emb xs1ys1 xs2ys2) too aggressively and fails to terminate
                    -- (at least in a reasonable amount of time), so we just mark this definition opaque
                    ++-×-lenfst-is-emb : {A : Set} → Is-emb (++-×-lenfst {A})
                    ++-×-lenfst-is-emb = is-equiv-then-is-emb ++-×-lenfst-is-eqv

                  -- These two functions are not definitionally equal, but pointwise they are.
                  tuple-++~fstfst∘++-×-lenfst : {A : Set} → tuple-++ {A} ~ ((Σ.fst ∘ Σ.fst) ∘ ++-×-lenfst)
                  tuple-++~fstfst∘++-×-lenfst (_ , _) = refl

                  ap-tuple-++-vs-ap-fst-ap-fst : {A : Set} → {xs1 xs2 ys1 ys2 : List A} → (β : (xs1 , ys1) ≡ (xs2 , ys2)) →
                                                 ap tuple-++ β ≡ ap Σ.fst (ap Σ.fst (ap ++-×-lenfst β))
                  ap-tuple-++-vs-ap-fst-ap-fst {A} {xs1} {xs2} {ys1} {ys2} β =
                    begin
                      ap tuple-++ β                                            ≡⟨← ·-runit _ ⟩
                      ap tuple-++ β · refl                                     ≡⟨⟩
                      ap tuple-++ β · tuple-++~fstfst∘++-×-lenfst (xs2 , ys2)  ≡⟨ nat-htpy tuple-++~fstfst∘++-×-lenfst β ⟩
                      tuple-++~fstfst∘++-×-lenfst (xs1 , ys1) · ap (((Σ.fst ∘ Σ.fst) ∘ ++-×-lenfst)) β
                                                                               ≡⟨⟩ -- because the homotopy is refl at each point
                      refl · ap (((Σ.fst ∘ Σ.fst) ∘ ++-×-lenfst)) β            ≡⟨⟩
                      ap (((Σ.fst ∘ Σ.fst) ∘ ++-×-lenfst)) β                   ≡⟨ ap-comp (Σ.fst ∘ Σ.fst) ++-×-lenfst β ⟩
                      ap (Σ.fst ∘ Σ.fst) (ap ++-×-lenfst β)                    ≡⟨ ap-comp Σ.fst Σ.fst (ap ++-×-lenfst β) ⟩
                      ap Σ.fst (ap Σ.fst (ap ++-×-lenfst β))                   ∎

        ... | right len-xs1≠len-xs2 =
                right (λ where (xs1ys1≡xs2ys2 , _) → (len-xs1≠len-xs2 (ap (length ∘ Σ.fst) xs1ys1≡xs2ys2)))

    tuple-++-is-0-trunc : {A : Set} → Is-trunc-map (succ-Trunc (succ-Trunc -2-Trunc)) (tuple-++ {A})
    tuple-++-is-0-trunc {A} zs = has-decidable-equality-then-is-set (fib-tuple-++-has-deceq zs)

  -- exercise 12.10
  module _ where
    is-sk-trunc-iff-const-is-k-trunc : {A : Set} → {k : TruncLevel} → Is-trunc (succ-Trunc k) A ↔ ((x : A) → Is-trunc-map k (const {Unit} x))
    is-sk-trunc-iff-const-is-k-trunc {A} {k} =
      begin-↔
        Is-trunc (succ-Trunc k) A                                               ↔⟨⟩
        ((x : A) → (y : A) → Is-trunc k (x ≡ y))                                ↔⟨← depfn-biimpl (λ x → depfn-biimpl (λ y →
                                                                                      equiv-then-k-type-iff-k-type
                                                                                        (Σ-lunit {B = λ _ → x ≡ y}))) ⟩
        ((x : A) → (y : A) → Is-trunc k (Σ Unit (λ _ → x ≡ y)))                 ↔⟨⟩
        ((x : A) → (y : A) → Is-trunc k (Σ Unit (λ a → const {Unit} x a ≡ y)))  ↔⟨⟩
        ((x : A) → Is-trunc-map k (const {Unit} x))                             ∎-↔

  -- exercise 12.11
  module _ where
    open HomotopyGroupoidSymbolic

    latter-is-k-trunc-then-comp-is-k-trunc-iff-first-is-k-trunc :
          {A B X : Set} → {k : TruncLevel} → {g : B → X} → Is-trunc-map k g →
          (h : A → B) → {f : A → X} → (H : f ~ g ∘ h) →
          Is-trunc-map k f ↔ Is-trunc-map k h
    latter-is-k-trunc-then-comp-is-k-trunc-iff-first-is-k-trunc {k = -2-Trunc} g-is--2-trunc h {f} H =
      begin-↔
        Is-trunc-map -2-Trunc f                 ↔⟨← is-equiv-iff-is-contr-fn ⟩
        Is-equiv f                              ↔⟨ latter-is-equiv-then-comp-is-equiv-iff-former-is-equiv h H (contr-fn-then-equiv g-is--2-trunc) ⟩
        Is-equiv h                              ↔⟨ is-equiv-iff-is-contr-fn ⟩
        Is-trunc-map -2-Trunc h                 ∎-↔
    latter-is-k-trunc-then-comp-is-k-trunc-iff-first-is-k-trunc {A} {B} {k = succ-Trunc k} {g = g} g-is-sk-trunc h {f} H =
      -- Idea:
      --   (a1 ≡ a2)  --(ap h)--> (h a1 ≡ h a2)
      --       │                        │
      --       │ ap f                   │ ap g
      --       │                        │
      --       v                        v
      -- (f a1 ≡ f a2) -(K)-> (g (h a1) ≡ g (h a2))
      --
      -- where the bottom arrow is an equivalence, and by IH and the fact that g is (k+1)-trunc,
      -- we have that K ∘ ap f is k-trunc iff ap h is. We remove the postcomposition by K and we are done.
      begin-↔
        Is-trunc-map (succ-Trunc k) f                        ↔⟨ map-is-sk-trunc-iff-ap-is-k-trunc ⟩
        ((x y : A) → Is-trunc-map k (ap f {x} {y}))          ↔⟨ depfn-biimpl-2 (λ (x y : A) → begin-↔
          Is-trunc-map k (ap f {x} {y})                        ↔⟨ postcomp-by-equiv-is-k-trunc-iff-original-is
                                                                    (ap f) (homotope-applied-is-equiv H x y) ⟩
          Is-trunc-map k (homotope-applied H x y ∘ ap f)       ↔⟨ latter-is-k-trunc-then-comp-is-k-trunc-iff-first-is-k-trunc
                                                                    {g = ap g {h x} {h y}}
                                                                    (apg-is-k-trunc x y) (ap h) (triangle-htpy x y) ⟩
          Is-trunc-map k (ap h)                                ∎-↔) ⟩
        ((x y : A) → Is-trunc-map k (ap h {x} {y}))          ↔⟨← map-is-sk-trunc-iff-ap-is-k-trunc ⟩
        Is-trunc-map (succ-Trunc k) h                        ∎-↔
      where
        apg-is-k-trunc : (x y : A) → Is-trunc-map k (ap g {h x} {h y})
        apg-is-k-trunc x y = Σ.fst map-is-sk-trunc-iff-ap-is-k-trunc g-is-sk-trunc (h x) (h y)

        triangle-htpy : (x y : A) → (homotope-applied H x y ∘ ap f) ~ (ap g ∘ ap h)
        triangle-htpy x y = homotope-applied-ap H x y ·ₕₜₚ ap-comp g h

    homotopy-preserves-truncatedness : {A B : Set} → {k : TruncLevel} → {f g : A → B} → (H : f ~ g) →
                                       Is-trunc-map k f → Is-trunc-map k g
    homotopy-preserves-truncatedness {A} {B} {k} {f} {g} H f-is-k-trunc =
      Σ.fst (latter-is-k-trunc-then-comp-is-k-trunc-iff-first-is-k-trunc
              {k = k} {g = id} (equiv-then-is-k-trunc-map id-is-equiv) g H)
            f-is-k-trunc

    homotopic-then-k-trunc-iff-k-trunc : {A B : Set} → {k : TruncLevel} → {f g : A → B} → (H : f ~ g) →
                                         Is-trunc-map k f ↔ Is-trunc-map k g
    homotopic-then-k-trunc-iff-k-trunc H =
      (homotopy-preserves-truncatedness H , homotopy-preserves-truncatedness (H ⁻¹ₕₜₚ))

  -- exercise 12.12
  module _ where
    is-family-of-k-trunc-iff-tot-is-k-trunc :
          {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x)
          {k : TruncLevel} → ((x : A) → Is-trunc-map k (f x)) ↔ Is-trunc-map k (totalization f)
    is-family-of-k-trunc-iff-tot-is-k-trunc {A} {B} {C} f {k} =
      -- note: this proof is just a proof of theorem 11.1.3 generalized to arbitrary truncation levels
      begin-↔
        ((x : A) → Is-trunc-map k (f x))                                    ↔⟨⟩
        ((x : A) → (c : C x) → Is-trunc k (fib (f x) c))                    ↔⟨← depfn-biimpl-2 (λ x c →
                                                                                  equiv-then-k-type-iff-k-type
                                                                                    (fib-tot-pt-equiv-fib-pr₁-pr₂ f (x , c))) ⟩
        ((x : A) → (c : C x) → Is-trunc k (fib (totalization f) (x , c)))   ↔⟨ uncurry-biimpl ⟩
        ((t : Σ A C) → Is-trunc k (fib (totalization f) t))                 ↔⟨⟩
        Is-trunc-map k (totalization f)                                     ∎-↔

  -- exercise 12.13
  module _ where
    prod-rmap-equiv : {A B C : Set} → B ≃ C → (A × B) ≃ (A × C)
    prod-rmap-equiv {A} {B} {C} (e , e-eqv) =
      build-tpe-equiv (conditionally-equivs-then-×₀-equiv
        (λ _ → id-is-equiv)
        (λ _ → e-eqv))

    fiber-incl : {A : Set} → (B : A → Set) → (a : A) → B a → Σ A B
    fiber-incl {A} B a b = (a , b)

    fib-of-unit-inclusion-≃-identity : {A : Set} → (x y : A) → (fib (fiber-incl (λ _ → Unit) x) (y , unit)) ≃ (x ≡ y)
    fib-of-unit-inclusion-≃-identity {A} x y =
      begin-≃
        fib (λ u → (x , u)) (y , unit)          ≃⟨⟩
        (Σ Unit (λ u → (x , u) ≡ (y , unit)))   ≃⟨ Σ-lunit ⟩
        ((x , unit) ≡ (y , unit))               ≃⟨ prod-eq-≃-eq-prod ⟩
        ((x ≡ y) × (unit ≡ unit))               ≃⟨ prod-rmap-equiv (contr-then-≃-Unit (Unit-is-prop unit unit)) ⟩
        ((x ≡ y) × Unit)                        ≃⟨ ×-runit ⟩
        (x ≡ y)                                 ∎-≃

    fiber-incl-is-k-trunc-then-sk-trunc : {A : Set} → {k : TruncLevel} →
          ((B : A → Set) → (a : A) → Is-trunc-map k (fiber-incl B a)) →
          Is-trunc (succ-Trunc k) A
    fiber-incl-is-k-trunc-then-sk-trunc {A} {k} assumption x y =
      -- Goal is (Is-trunc k (x ≡ y)), so fib-of-unit-inclusion-≃-identity is exactly what we need
      equiv-to-k-type-then-is-k-type
        (fib-of-unit-inclusion-≃-identity x y)
        (assumption (λ _ → Unit) x (y , unit))

    sk-trunc-then-fiber-incl-is-k-trunc : {A : Set} → {k : TruncLevel} → Is-trunc (succ-Trunc k) A →
          (B : A → Set) → (a : A) →
          Is-trunc-map k (fiber-incl B a)
    sk-trunc-then-fiber-incl-is-k-trunc {A} { -2-Trunc } a-is-prop B a =
      let a-is-contr : Is-contr A
          a-is-contr = Is-prop-characterisation.i→iii a-is-prop a
      in
        is-equiv-then-is-contr-fn
          (base-is-contr-then-pair-with-base-is-equiv (a , recenter-contraction-at a a-is-contr))
    sk-trunc-then-fiber-incl-is-k-trunc {A} { succ-Trunc k } a-is-sk-trunc B a =
      let motive-equivalence =
            begin-↔
              Is-trunc-map (succ-Trunc k) (fiber-incl B a)                      ↔⟨ map-is-sk-trunc-iff-ap-is-k-trunc ⟩
              ((b1 b2 : B a) → Is-trunc-map k (ap (fiber-incl B a) {b1} {b2}))  ↔⟨ depfn-biimpl-2 (λ (b1 b2 : B a) → begin-↔
                Is-trunc-map k (ap (fiber-incl B a) {b1} {b2})                                    ↔⟨ homotopic-then-k-trunc-iff-k-trunc (ap-fiber-incl-factorization b1 b2) ⟩
                Is-trunc-map k ( eq-pair (a , b1) (a , b2) ∘ fiber-incl (Eq-over-tr b1 b2) refl)  ↔⟨← postcomp-by-equiv-is-k-trunc-iff-original-is
                                                                                                        (fiber-incl (Eq-over-tr b1 b2) refl)
                                                                                                        (eq-pair-is-equiv {s = (a , b1)} {t = (a , b2)}) ⟩
                Is-trunc-map k (fiber-incl (Eq-over-tr b1 b2) refl)                               ∎-↔) ⟩
              ((b1 b2 : B a) → Is-trunc-map k (fiber-incl (Eq-over-tr b1 b2) refl))
                                                                                ∎-↔
      in (Σ.snd motive-equivalence) fiber-incl-to-Eq-Σ-is-k-trunc
      where
        Eq-over-tr : {a : A} → (b1 b2 : B a) → (α : a ≡ a) → Set
        Eq-over-tr {a} b1 b2 α = tr B α b1 ≡ b2

        ap-fiber-incl-factorization : (b1 b2 : B a) →
              ap (fiber-incl B a) {b1} {b2} ~ (eq-pair (a , b1) (a , b2) ∘ fiber-incl (Eq-over-tr b1 b2) refl)
        ap-fiber-incl-factorization b1 .b1 refl = refl

        fiber-incl-to-Eq-Σ-is-k-trunc : (b1 b2 : B a) → Is-trunc-map k (fiber-incl (Eq-over-tr b1 b2) refl)
        fiber-incl-to-Eq-Σ-is-k-trunc b1 b2 =
          sk-trunc-then-fiber-incl-is-k-trunc (a-is-sk-trunc a a) (Eq-over-tr b1 b2) refl

  -- exercise 12.14
  module _ where
    Is-isolated : {A : Set} → (a : A) → Set
    Is-isolated {A} a = (x : A) → ((a ≡ x) +₀ (a ≢ x))

    -- exercise 12.14.a
    is-isolated-iff-picking-map-has-dec-fibers : {A : Set} → (a : A) → Is-isolated a ↔ ((x : A) → Is-decidable (fib (const {Unit} a) x))
    is-isolated-iff-picking-map-has-dec-fibers {A} a = {!   !}

    -- exercise 12.14.b
    is-isolated-then-identity-is-prop : {A : Set} → (a : A) → Is-isolated a → (x : A) → Is-prop (a ≡ x)
    is-isolated-then-identity-is-prop {A} a is-isolated x = {!   !}

    is-isolated-then-picking-map-is-emb : {A : Set} → (a : A) → Is-isolated a → Is-emb (const {Unit} a)
    is-isolated-then-picking-map-is-emb {A} a is-isolated = {!   !}
