open import Function.Base using (case_of_)

module _ where
  open import section-11 public

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
  Is-contr-then-is-prop : {A : Set} → Is-contr A → Is-prop A
  Is-contr-then-is-prop contr = Is-contr-then-identity-is-contr contr

  Unit-Is-prop : Is-prop Unit
  Unit-Is-prop = Is-contr-then-is-prop Unit-Is-contr

  Empty-Is-prop : Is-prop Empty
  Empty-Is-prop _ ()

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
      cod-of-equiv-is-contr-then-dom-is-contr (const-is-emb x y) (Unit-Is-prop unit unit)

    ii→i : ii → i
    ii→i = iv→i ∘ iii→iv ∘ ii→iii

    i↔iii : i ↔ iii
    i↔iii = (ii→iii ∘ i→ii , iv→i ∘ iii→iv)

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

  props-equiv-iff-biimpl : ((P , PProp) (Q , QProp) : Props _) → (P ≃ Q) ↔ (P ↔ Q)
  props-equiv-iff-biimpl P Q =
    (
      (λ { (map , eqv) → (map , Σ.fst (map-between-props-is-equiv-iff-converse P Q map) eqv) }),
      (λ { (forward , backward) → (forward , Σ.snd (map-between-props-is-equiv-iff-converse P Q forward) backward) })
    )
  
  -- definition 12.2.1
  Is-subtype : {A : Set} → (B : A → Set) → Set
  Is-subtype {A} B = (x : A) → Is-prop (B x)

  -- lemma 12.2.2
  Is-prop-pulled-back-by-equiv : {A B : Set} → {f : A → B} → Is-equiv f → Is-prop B → Is-prop A
  Is-prop-pulled-back-by-equiv {A} {B} {f} equiv is-prop x y =
    cod-of-equiv-is-contr-then-dom-is-contr
      (is-equiv-then-is-emb equiv x y)
      (is-prop (f x) (f y))

  Is-prop-preserved-by-equiv : {A B : Set} → {f : A → B} → Is-equiv f → Is-prop A → Is-prop B
  Is-prop-preserved-by-equiv {A} {B} {f} equiv is-prop =
    Is-prop-pulled-back-by-equiv (≃-inverse-map-is-equiv equiv) is-prop

  dom-of-equiv-is-prop-iff-cod-is-prop : {A B : Set} → {f : A → B} → Is-equiv f → Is-prop A ↔ Is-prop B
  dom-of-equiv-is-prop-iff-cod-is-prop {A} {B} {f} equiv =
    (Is-prop-preserved-by-equiv equiv , Is-prop-pulled-back-by-equiv equiv)

  open ↔-Reasoning

  -- theorem 12.2.3
  module _ where
    ap-is-equiv-iff-ap-inverse-if-equiv : {A B : Set} → {f : A → B} → (x y : A) → Is-equiv (ap f {x} {y}) ↔ Is-equiv (λ p → ap f {x} {y} (inverse p))
    ap-is-equiv-iff-ap-inverse-if-equiv x y =
      (
        (λ eqv → comp-equivs-is-equiv eqv EqualityOps.inv-is-equiv)
      , (λ eqv → former-and-comp-are-equivs-then-latter-is-equiv (λ { refl → refl }) EqualityOps.inv-is-equiv eqv)
      )

    -- NOTE: It looks like Lemma 12.2.2 is not involved in the proof.
    is-emb-iff-fibs-are-props : {A B : Set} → {f : A → B} → Is-emb f ↔ ((b : B) → Is-prop (fib f b))
    is-emb-iff-fibs-are-props {A} {B} {f} =
      begin-↔
        Is-emb f                                                            ↔⟨⟩
        ((x : A) → (y : A) → Is-equiv (λ (p : x ≡ y) → ap f p))             ↔⟨ depfn-iff (λ x → depfn-iff (λ y → ap-is-equiv-iff-ap-inverse-if-equiv x y)) ⟩
        ((x : A) → (y : A) → Is-equiv (λ (p : y ≡ x) → ap f (inverse p)))   ↔⟨ flip-dependent-iff ⟩
        ((y : A) → (x : A) → Is-equiv (λ (p : y ≡ x) → ap f (inverse p)))   ↔⟨ depfn-iff (λ y → fundamental-thm-of-identity-types.i-at-fn↔ii (λ x (p : y ≡ x) → ap f (inverse p))) ⟩
        ((y : A) → Is-contr (Σ A (λ x → f x ≡ f y)))                        ↔⟨⟩
        ((y : A) → Is-contr (fib f (f y)))                                  ↔⟨ depfn-iff (λ y → ((λ contr b p → tr _ p contr) , (λ contr → contr (f y) refl))) ⟩
        ((y : A) → (b : B) → (p : f y ≡ b) → Is-contr (fib f b))            ↔⟨ flip-dependent-iff ⟩
        ((b : B) → (y : A) → (p : f y ≡ b) → Is-contr (fib f b))            ↔⟨ depfn-iff (λ b → uncurry-iff) ⟩
        ((b : B) → fib f b → Is-contr (fib f b))                            ↔⟨← depfn-iff (λ b → Is-prop-characterisation.i↔iii) ⟩
        ((b : B) → Is-prop (fib f b))                                       ∎-↔

  -- corollary 12.2.4
  fst-is-emb-iff-is-subtype : {A : Set} → {B : A → Set} → Is-emb (Σ.fst {A} {B}) ↔ Is-subtype B
  fst-is-emb-iff-is-subtype {A} {B} =
    begin-↔
      Is-emb (Σ.fst {A} {B})                           ↔⟨ is-emb-iff-fibs-are-props ⟩
      ((x : A) → Is-prop (fib (Σ.fst {A} {B}) x))      ↔⟨ depfn-iff (λ x → dom-of-equiv-is-prop-iff-cod-is-prop (tr-from-fib-pr1-is-equiv x)) ⟩
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
  Eq-Nat-is-prop zero zero         = Unit-Is-prop
  Eq-Nat-is-prop zero (succ m)     = Empty-Is-prop
  Eq-Nat-is-prop (succ n) zero     = Empty-Is-prop
  Eq-Nat-is-prop (succ n) (succ m) = Eq-Nat-is-prop n m

  Nat-is-set : Is-set Nat
  Nat-is-set = λ n m → Is-prop-pulled-back-by-equiv (Eq-Nat-refl-is-equiv n m) (Eq-Nat-is-prop n m)

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
          (identity-with-an-endpoint-fixed-Is-contr x)

  underlying-type-of-reflexive-propositional-relation-is-set :
    {A : Set} → (R : A → A → Set) →
    (reflexive : (x : A) → R x x) →
    (propositional : (x y : A) → Is-prop (R x y)) →
    (maps-into-identity-types : (x y : A) → R x y → x ≡ y) →
    Is-set A    
  underlying-type-of-reflexive-propositional-relation-is-set
      {A} R reflexive propositional maps-into-identity-types x y =
    Is-prop-pulled-back-by-equiv
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
      ...                      | (left p)      = Unit-Is-prop
      ...                      | (right ¬p)    = Empty-Is-prop

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
  k-type-is-a-succ-k-type : {A : Set} → {k : TruncLevel} → Is-trunc k A → Is-trunc (succ-Trunc k) A
  k-type-is-a-succ-k-type {A} { -2-Trunc } A-is-contr = Is-contr-then-is-prop A-is-contr
  k-type-is-a-succ-k-type {A} { (succ-Trunc k) } A-is-sk-trunc x y = k-type-is-a-succ-k-type (A-is-sk-trunc x y)

  -- corollary 12.4.4
  identity-type-of-a-k-type-is-a-k-type : {A : Set} → {k : TruncLevel} → Is-trunc k A → (x y : A) → Is-trunc k (x ≡ y)
  identity-type-of-a-k-type-is-a-k-type {A} {k} = k-type-is-a-succ-k-type

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

