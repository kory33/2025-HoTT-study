open import Function.Base using (case_of_)

module _ where
  open import section-03 public

  -- definition 4.2.1
  data Unit : Set where
    unit : Unit

  Unit-ind : {P : Unit → Set} → P unit → (x : Unit) → P x 
  Unit-ind pu unit = pu

  -- definition 4.3.1
  data Empty : Set where

  Empty-ind : {P : Empty → Set} → (x : Empty) → P x
  Empty-ind ()

  module EmptyBasic where
    -- alias
    absurd : {A : Set} → Empty → A
    absurd = Empty-ind

    -- alias
    ex-falso : {A : Set} → Empty → A
    ex-falso = absurd

    -- definition 4.3.2
    Is-empty : Set → Set
    Is-empty A = A → Empty

    -- definition 4.3.2
    ¬_ : Set → Set
    ¬ A = A → Empty

    infix 50 ¬_

    -- proposition 4.3.4
    contrapose : {A B : Set} → (A → B) → ¬ B → ¬ A
    contrapose f ¬b a = ¬b (f a)

  -- definition 4.4.1
  data _+₀_ (A B : Set) : Set where
    left : A → A +₀ B
    right : B → A +₀ B
  infixl 30 _+₀_

  ind-+₀ : {A B : Set} → (P : A +₀ B → Set) → ((x : A) → P(left x)) → ((y : B) → P(right y)) → (z : A +₀ B) → P z
  ind-+₀ P pL pR (left x) = pL x
  ind-+₀ P pL pR (right y) = pR y

  module +₀-Basic where
    open EmptyBasic

    -- definition 4.4.2
    <_+₀_> : {A B A' B' : Set} → (A → A') → (B → B') → (A +₀ B) → (A' +₀ B')
    < f +₀ g > = ind-+₀ _ (λ x → left (f x)) (λ y → right (g y))

    [_+₀_] : {A B C : Set} → (f : A → C) → (g : B → C) → (A +₀ B) → C
    [_+₀_] f g = ind-+₀ _ (λ x → f x) (λ y → g y)

    -- proposition 4.4.3
    +₀-empty-right : {A B : Set} → Is-empty B → A +₀ B → A
    +₀-empty-right ¬b (left x) = x
    +₀-empty-right ¬b (right y) = absurd (¬b y)

    +₀-empty-left : {A B : Set} → Is-empty A → A +₀ B → B
    +₀-empty-left ¬a (left x) = absurd (¬a x)
    +₀-empty-left ¬a (right y) = y

    swap-+₀ : {X Y : Set} → X +₀ Y → Y +₀ X
    swap-+₀ (left x)  = right x
    swap-+₀ (right y) = left y

    leftMap : {A B A' : Set} → (A → A') → (A +₀ B) → (A' +₀ B)
    leftMap f = < f +₀ id >

    mapLeftOf : {A B A' : Set} → (A +₀ B) → (A → A') → (A' +₀ B)
    mapLeftOf = swap leftMap

    rightMap : {A B B' : Set} → (B → B') → (A +₀ B) → (A +₀ B')
    rightMap g = < id +₀ g >

    mapRightOf : {A B B' : Set} → (A +₀ B) → (B → B') → (A +₀ B')
    mapRightOf = swap rightMap

  -- definition 4.6.1, made universe-polymorphic for use in section 11
  open import Agda.Primitive
  record Σ-poly {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
    -- Turn off eta equality (since the book does not assume the eta rule for Σ-types)
    no-eta-equality
    -- ... but allow pattern matching for induction
    pattern
    constructor pair
    field
      fst : A
      snd : B fst
  
  Σ : (A : Set) → (B : A → Set) → Set
  Σ A B = Σ-poly A B

  module Σ where
    -- definition 4.6.2
    fst : {A : Set} → {B : A → Set} → Σ A B → A
    fst (pair x y) = x

    snd : {A : Set} → {B : A → Set} → (t : Σ A B) → B (fst t)
    snd (pair x y) = y

  ind-Σ : {A : Set} → {B : A → Set} → {P : (x : Σ A B) → Set} →
          ((x : A) → (y : B x) → P (pair x y)) →
          (z : Σ A B) → P z
  ind-Σ pXY (pair x y) = pXY x y

  module Σ-Basic where
    module Symbolic where
      pattern _,_ a b = pair a b
      infixr 15 _,_
    open Symbolic

    pr₁ : {A : Set} → {B : A → Set} → Σ A B → A
    pr₁ (x , y) = x

    pr₂ : {A : Set} → {B : A → Set} → (p : Σ A B) → B (pr₁ p)
    pr₂ (x , y) = y

    -- definition 4.6.3
    curry : {A : Set} → {B : A → Set} → {P : Σ A B → Set} →
            ((z : Σ A B) → P z) →
            (x : A) → (y : B x) → P (x , y)
    curry p x y = p (x , y)

    uncurry : {A : Set} → {B : A → Set} → {P : Σ A B → Set} →
              ((x : A) → (y : B x) → P (x , y)) →
              (z : Σ A B) → P z
    uncurry = ind-Σ

  open Σ-Basic.Symbolic public

  -- definition 4.6.4
  _×_ : (A B : Set) → Set
  A × B = Σ A (λ x → B)
  infixr 15 _×_

  -- remark 4.6.5
  ind-× : {A B : Set} → {P : A × B → Set} →
          ((x : A) → (y : B) → P (x , y)) →
          (z : A × B) → P z
  ind-× pXY (x , y) = pXY x y

  -- definition 4.5.1
  Int = Nat +₀ (Unit +₀ Nat)

  module IntBasic where
    pattern zeroInt = right (left unit)
    pattern posSucc n = right (right n)
    pattern negSucc n = left n

    -- definition 4.5.3
    Int-succ : Int → Int
    Int-succ zeroInt = posSucc zero
    Int-succ (posSucc n) = posSucc (succ n)
    Int-succ (negSucc zero) = zeroInt
    Int-succ (negSucc (succ n)) = negSucc n

    Int-one : Int
    Int-one = posSucc zero

    -- exercise 4.1.a
    pred : Int → Int
    pred zeroInt = negSucc zero
    pred (posSucc zero) = zeroInt
    pred (posSucc (succ n)) = posSucc n
    pred (negSucc n) = negSucc (succ n)

    abs : Int → Nat
    abs zeroInt = zero
    abs (posSucc n) = succ n
    abs (negSucc n) = n

    posOrZeroOfNat : Nat → Int
    posOrZeroOfNat zero = zeroInt
    posOrZeroOfNat (succ n) = posSucc n

    negOrZeroOfNat : Nat → Int
    negOrZeroOfNat zero = zeroInt
    negOrZeroOfNat (succ n) = negSucc n

    -- exercise 4.1.b
    Nat-minus : Nat → Nat → Int
    Nat-minus zero zero = zeroInt
    Nat-minus zero (succ n) = negSucc n
    Nat-minus (succ n) zero = posSucc n
    Nat-minus (succ n) (succ m) = Nat-minus n m

    asNatDiff : Int → (Nat × Nat)
    asNatDiff zeroInt = (zero , zero)
    asNatDiff (posSucc n) = ((succ n), zero)
    asNatDiff (negSucc n) = (zero , (succ n))
     
    add : Int → Int → Int
    add n m = let (n₊ , n₋) = asNatDiff n
                  (m₊ , m₋) = asNatDiff m
              in Nat-minus (NatBasic.add n₊ m₊) (NatBasic.add n₋ m₋)

    -- exercise 4.1.b
    neg : Int → Int
    neg n = let (n₊ , n₋) = asNatDiff n in Nat-minus n₋ n₊

    -- exercise 4.1.c
    mul : Int → Int → Int
    mul n m = let (n₊ , n₋) = asNatDiff n
                  (m₊ , m₋) = asNatDiff m
              in Nat-minus
                (NatBasic.add (NatBasic.mul n₊ m₊) (NatBasic.mul n₋ m₋))
                (NatBasic.add (NatBasic.mul n₊ m₋) (NatBasic.mul n₋ m₊))

    module Symbolic where
      _+_ : Int → Int → Int
      _+_ = add
      infixl 35 _+_

      _*_ : Int → Int → Int
      _*_ = mul
      infixl 40 _*_

      _-_ : Int → Int → Int
      x - y = add x (neg y)
      infixl 35 _-_

      -_ : Int → Int
      -_ = neg
      infixl 50 -_

    module SymbolicQualified where
      _-ℕ_ : Nat → Nat → Int
      _-ℕ_ = Nat-minus
      infixl 35 _-ℕ_

      _+ℤ_ : Int → Int → Int
      _+ℤ_ = add
      infixl 35 _+ℤ_

      _*ℤ_ : Int → Int → Int
      _*ℤ_ = mul
      infixl 40 _*ℤ_

      -ℤ_ : Int → Int
      -ℤ_ = neg
      infixl 50 -ℤ_

  data Bool : Set where
    true false : Bool
  
  ind-Bool : {P : Bool → Set} →
             (pT : P true) → (pF : P false) →
             (b : Bool) → P b
  ind-Bool pT pF true = pT
  ind-Bool pT pF false = pF

  module Bool-If-Syntax where
    if_then_else_ : (b : Bool) → {P : Bool → Set} →
                    (pT : P true) → (pF : P false) →
                    P b
    if_then_else_ b {P} pT pF = ind-Bool {P} pT pF b
  open Bool-If-Syntax public

  module BoolBasic where
    -- exercise 4.2.a
    neg-bool : Bool → Bool
    neg-bool true = false
    neg-bool false = true

    _∧_ : Bool → Bool → Bool
    true ∧ true = true
    true ∧ false = false
    false ∧ true = false
    false ∧ false = false

    _∨_ : Bool → Bool → Bool
    true ∨ true = true
    true ∨ false = true
    false ∨ true = true
    false ∨ false = false

  _↔-poly_ : {i j : Level} → Set i → Set j → Set (i ⊔ j)
  A ↔-poly B = Σ-poly (A → B) (λ _ → B → A)

  _↔_ : Set → Set → Set
  A ↔ B = A ↔-poly B

  module ↔-Basic where
    flip-biimpl : {i j : Level} → {A : Set i} → {B : Set j} → (A ↔-poly B) → (B ↔-poly A)
    flip-biimpl (a→b , b→a) = (b→a , a→b)

    trans-biimpl : {i j k : Level} → {A : Set i} → {B : Set j} → {C : Set k} → (A ↔-poly B) → (B ↔-poly C) → (A ↔-poly C)
    trans-biimpl (a→b , b→a) (b→c , c→b) = ((λ a → b→c (a→b a)), (λ c → b→a (c→b c)))

    prod-biimpl : {A B C D : Set} → (A ↔ B) → (C ↔ D) → ((A × C) ↔ (B × D))
    prod-biimpl (a→b , b→a) (c→d , d→c) = ((λ { (a , c) → ((a→b a), (c→d c)) }), (λ { (b , d) → ((b→a b), (d→c d)) }))

    depfn-biimpl : {i j : Level} → {A : Set i} → {B C : A → Set j} → (foralla : (x : A) → (B x ↔-poly C x)) →
                ((x : A) → B x) ↔-poly ((x : A) → C x)
    depfn-biimpl foralla = ((λ f x → Σ-poly.fst (foralla x) (f x)) , λ f x → Σ-poly.snd (foralla x) (f x))

    depfn-biimpl-2 : {i j : Level} → {A0 : Set i} → {A1 : A0 → Set j} → {B C : (a0 : A0) → (a1 : A1 a0) → Set} →
                  (foralla0a1 : (x : A0) → (y : A1 x) → (B x y ↔-poly C x y)) →
                  ((x : A0) → (y : A1 x) → B x y) ↔-poly ((x : A0) → (y : A1 x) → C x y)
    depfn-biimpl-2 foralla0a1 = ((λ f x y → Σ-poly.fst (foralla0a1 x y) (f x y)) , λ f x y → Σ-poly.snd (foralla0a1 x y) (f x y))

    uncurry-biimpl : {A : Set} → {B : A → Set} → {C : Σ A B → Set} →
                  (((x : A) → (y : B x) → C (x , y)) ↔ ((z : Σ A B) → C z))
    uncurry-biimpl = ((λ { f (a , b) → f a b }) , (λ f a b → f (a , b)))

    open EmptyBasic
    neg-biimpl : {A B : Set} → (A ↔ B) → (¬ A ↔ ¬ B)
    neg-biimpl (a→b , b→a) = ((contrapose b→a), (contrapose a→b))

  module ↔-Reasoning where
    open ↔-Basic public

    infix  1 begin-↔_
    infixr 2 step-↔-∣ step-↔-⟩ step-↔-⟩⁻¹
    infix  3 _∎-↔

    begin-↔_ : {x y : Set} → (x ↔ y) → (x ↔ y)
    begin-↔ x↔y = x↔y

    step-↔-∣ : (x : Set) → {y : Set} → (x ↔ y) → (x ↔ y)
    step-↔-∣ x x↔y = x↔y

    step-↔-⟩ : (x : Set) → {y z : Set} → (y ↔ z) → (x ↔ y) → (x ↔ z)
    step-↔-⟩ x y↔z x↔y = trans-biimpl x↔y y↔z

    step-↔-⟩⁻¹ : (x : Set) → {y z : Set} → (y ↔ z) → (y ↔ x) → (x ↔ z)
    step-↔-⟩⁻¹ x y↔z y↔x = trans-biimpl (flip-biimpl y↔x) y↔z

    syntax step-↔-∣ x x↔y       =  x ↔⟨⟩ x↔y
    syntax step-↔-⟩ x y↔z x↔y   =  x ↔⟨ x↔y ⟩ y↔z
    syntax step-↔-⟩⁻¹ x y↔z y↔x =  x ↔⟨← y↔x ⟩ y↔z

    _∎-↔ : (x : Set) → (x ↔ x)
    x ∎-↔  =  (id , id)

  module ↔-poly-Reasoning where
    open ↔-Basic

    infix  1 begin-↔-poly_
    infixr 2 step-↔-poly-∣ step-↔-poly-⟩ step-↔-poly-⟩⁻¹
    infix  3 _∎-↔-poly

    begin-↔-poly_ : {i j : Level} → {x : Set i} → {y : Set j} → (x ↔-poly y) → (x ↔-poly y)
    begin-↔-poly x↔y = x↔y

    step-↔-poly-∣ : {i j : Level} → (x : Set i) → {y : Set j} → (x ↔-poly y) → (x ↔-poly y)
    step-↔-poly-∣ x x↔y = x↔y

    step-↔-poly-⟩ : {i j k : Level} → (x : Set i) → {y : Set j} → {z : Set k} → (y ↔-poly z) → (x ↔-poly y) → (x ↔-poly z)
    step-↔-poly-⟩ x y↔z x↔y = trans-biimpl x↔y y↔z

    step-↔-poly-⟩⁻¹ : {i j k : Level} → (x : Set i) → {y : Set j} → {z : Set k} → (y ↔-poly z) → (y ↔-poly x) → (x ↔-poly z)
    step-↔-poly-⟩⁻¹ x y↔z y↔x = trans-biimpl (flip-biimpl y↔x) y↔z

    syntax step-↔-poly-∣ x x↔y       =  x ↔-poly⟨⟩ x↔y
    syntax step-↔-poly-⟩ x y↔z x↔y   =  x ↔-poly⟨ x↔y ⟩ y↔z
    syntax step-↔-poly-⟩⁻¹ x y↔z y↔x =  x ↔-poly⟨← y↔x ⟩ y↔z

    _∎-↔-poly : {i : Level} → (x : Set i) → (x ↔-poly x)
    x ∎-↔-poly = ((λ x → x) , (λ x → x))

  -- exercise 4.3
  module exercise-4-3 where
    open EmptyBasic
    open Σ
    open Σ-Basic

    ¬¬_ : Set → Set
    ¬¬_ A = ¬ ¬ A
    infix 50 ¬¬_

    biimpl : {A B : Set} → (A ↔ B) → (A ↔ B)
    biimpl p = p

    -- exercise 4.3.a.i
    ex-a-i : {P : Set} → ¬ (P × ¬ P)
    ex-a-i p×¬p = (snd p×¬p) (fst p×¬p)

    -- exercise 4.3.a.ii
    ex-a-ii : {P : Set} → ¬ (P ↔ ¬ P)
    ex-a-ii p↔¬p = do
      let ¬p = λ p → (fst p↔¬p) p p
          p = (snd p↔¬p) ¬p
      ¬p p

    -- exercise 4.3.b.i
    ex-b-i : {P : Set} → P → ¬¬ P
    ex-b-i p ¬p = ¬p p

    -- exercise 4.3.b.ii
    ex-b-ii : {P Q : Set} → (P → Q) → (¬¬ P → ¬¬ Q)
    ex-b-ii p→q ¬¬p ¬q = ¬¬p (λ p → ¬q (p→q p))

    -- exercise 4.3.b.iii
    ex-b-iii : {P Q : Set} → (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
    ex-b-iii p→¬¬q ¬¬p ¬q = ¬¬p (λ p → p→¬¬q p ¬q)

    pure : {P : Set} → P → ¬¬ P
    pure = ex-b-i

    map : {P Q : Set} → (P → Q) → ¬¬ P → ¬¬ Q
    map = ex-b-ii

    _>>=_ : {P Q : Set} → ¬¬ P → (P → ¬¬ Q) → ¬¬ Q
    ¬¬p >>= next = ex-b-iii next ¬¬p

    _<*>_ : {P Q : Set} → ¬¬(P → Q) → ¬¬ P → ¬¬ Q
    ¬¬pq <*> ¬¬p = do
      pq ← ¬¬pq
      p ← ¬¬p
      pure (pq p)

    ⊥ : Set
    ⊥ = Empty

    -- some intuitive lemmas
    not-bot : ¬ ⊥
    not-bot = id
    
    not-not-not-bot : ¬ ¬ ¬ ⊥
    not-not-not-bot = ex-b-i not-bot

    -- exercise 4.3.c.i
    ex-c-i : {P : Set} → ¬¬ (¬¬ P → P)
    ex-c-i ¬DNE = ¬DNE (λ ¬¬p → absurd (¬¬p (λ p → ¬DNE (λ _ → p))))

    -- exercise 4.3.c.ii
    ex-c-ii : {P Q : Set} → ¬¬ (((P → Q) → P) → P)
    ex-c-ii not-peirce-law =
      not-peirce-law (λ pqpp →
        pqpp (λ p →
          absurd (not-peirce-law (λ _ → p))
        )
      )

    -- exercise 4.3.c.iii
    ex-c-iii : {P Q : Set} → ¬¬ ((P → Q) +₀ (Q → P))
    ex-c-iii not-dummett-law =
      not-dummett-law (left (λ p → absurd (not-dummett-law (right (λ _ → p)))))

    -- exercise 4.3.c.iv
    ex-c-iv : {P : Set} → ¬¬ (P +₀ ¬ P)
    ex-c-iv {P} = do
      p→¬p∨¬p→p ← ex-c-iii {P} {¬ P}
      case p→¬p∨¬p→p of λ
        { (left p→¬p) →
            let ¬p = λ p → p→¬p p p
            in pure (right ¬p)
        ; (right ¬p→p) →
            let ¬¬p = λ ¬p → ¬p (¬p→p ¬p)
            in map left ¬¬p
        }

    -- exercise 4.3.d.i
    ex-d-i : {P : Set} → (P +₀ ¬ P) → (¬¬ P → P)
    ex-d-i (left p) ¬¬p = p
    ex-d-i (right ¬p) ¬¬p = absurd (¬¬p ¬p)

    -- exercise 4.3.d.ii
    ex-d-ii : {P Q : Set} → (¬¬(Q → P)) ↔ ((P +₀ ¬ P) → (Q → P))
    ex-d-ii =
      biimpl (
        (λ ¬¬qp lem q → case lem of λ
          { (left p) → p
          ; (right ¬p) → absurd (¬¬qp (λ qp → ¬p (qp q)))
          }),
        (λ lemToQ→P → map lemToQ→P ex-c-iv)
      )

    -- exercise 4.3.e.i
    ex-e-i : {P : Set} → ¬ ¬ ¬ P → ¬ P
    ex-e-i ¬¬¬p p = ¬¬¬p (λ ¬p → ¬p p)

    -- exercise 4.3.e.ii
    ex-e-ii : {P Q : Set} → ¬¬(P → ¬¬ Q) → (P → ¬¬ Q)
    ex-e-ii ¬¬p→¬¬q p = do
      p→¬¬q ← ¬¬p→¬¬q
      q ← p→¬¬q p
      pure q

    -- exercise 4.3.e.iii
    ex-e-iii : {P Q : Set} → ¬¬((¬¬ P) × (¬¬ Q)) → ¬¬ P × ¬¬ Q
    ex-e-iii ¬¬-pair = ((¬¬-pair >>= pr₁), (¬¬-pair >>= pr₂))

    -- exercise 4.3.f.i
    ex-f-i : {P Q : Set} → ¬¬(P × Q) ↔ (¬¬ P × ¬¬ Q)
    ex-f-i =
      biimpl (
        (λ ¬¬pq → ((map pr₁ ¬¬pq), (map pr₂ ¬¬pq))),
        (λ { (¬¬p , ¬¬q) → do
          p ← ¬¬p
          q ← ¬¬q
          pure (p , q)
        })
      )

    ex-f-ii' : {P Q : Set} → ¬ (P +₀ Q) ↔ (¬ P × ¬ Q)
    ex-f-ii' =
      biimpl (
        (λ ¬p∨q → ((λ p → ¬p∨q (left p)), (λ q → ¬p∨q (right q)))),
        (λ { (¬p , _) (left p) → ¬p p ; (_ , ¬q) (right q) → ¬q q })
      )

    ↔-neg-of-↔ : {P Q : Set} → (P ↔ Q) → (¬ P ↔ ¬ Q)
    ↔-neg-of-↔ (p→q , q→p) = ((contrapose q→p), (contrapose p→q))

    -- exercise 4.3.f.ii
    ex-f-ii : {P Q : Set} → ¬¬(P +₀ Q) ↔ ¬(¬ P × ¬ Q)
    ex-f-ii = ↔-neg-of-↔ ex-f-ii'

    -- exercise 4.3.f.iii
    ex-f-iii : {P Q : Set} → ¬¬(P → Q) ↔ (¬¬ P → ¬¬ Q)
    ex-f-iii =
      biimpl (
        (_<*>_),
        (λ ¬¬p→¬¬q ¬p→q →
          absurd (¬p→q (λ p →
            absurd (
              ¬¬p→¬¬q (λ ¬p → ¬p p) (λ q → ¬p→q (λ _ → q))
            )
          ))
        )
      )

  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A
  
  -- exercise 4.4.a
  ind-List : {A : Set} → {P : List A → Set} →
             (pNil : P nil) →
             ((x : A) (xs : List A) → P xs → P (cons x xs)) →
             (z : List A) → P z
  ind-List pNil pCons nil = pNil
  ind-List pNil pCons (cons x xs) = pCons x xs (ind-List pNil pCons xs)

  module List-Basic where
    -- exercise 4.4.b
    fold : {A B : Set} → B → (A → B → B) → List A → B
    fold b f nil = b
    fold b f (cons x xs) = f x (fold b f xs)

    -- exercise 4.4.c
    map : {A B : Set} → (A → B) → List A → List B
    map f nil = nil
    map f (cons x xs) = cons (f x) (map f xs)

    -- exercise 4.4.d
    length : {A : Set} → List A → Nat
    length nil = zero
    length (cons _ xs) = succ (length xs)

    -- exercise 4.4.e
    sum : List Nat → Nat
    sum nil = zero
    sum (cons x xs) = NatBasic.add x (sum xs)
    
    product : List Nat → Nat
    product nil = NatBasic.one
    product (cons x xs) = NatBasic.mul x (product xs)

    -- exercise 4.4.f
    concat : {A : Set} → List A → List A → List A
    concat nil ys = ys
    concat (cons x xs) ys = cons x (concat xs ys)

    -- exercise 4.4.g
    flatten : {A : Set} → List (List A) → List A
    flatten nil = nil
    flatten (cons xs xss) = concat xs (flatten xss)

    -- exercise 4.4.h
    reverse : {A : Set} → List A → List A
    reverse = go nil where
      go : {A : Set} → List A → List A → List A
      go acc nil = acc
      go acc (cons x xs) = go (cons x acc) xs
