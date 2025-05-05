open import section-2
open import section-3

open import Function.Base using (case_of_)

module _ where
  -- 4.2
  data Unit : Set where
    unit : Unit

  Unit-ind : {P : Unit → Set} → P unit → (x : Unit) → P x 
  Unit-ind pu unit = pu

  -- 4.3
  data Empty : Set where

  Enpty-ind : {P : Empty → Set} → (x : Empty) → P x
  Enpty-ind ()

  module EmptyBasic where
    -- alias
    absurd : {A : Set} → Empty → A
    absurd = Enpty-ind

    -- alias
    ex-falso : {A : Set} → Empty → A
    ex-falso = absurd

    is-empty : Set → Set
    is-empty A = A → Empty

    ¬_ : Set → Set
    ¬ A = A → Empty

    infix 50 ¬_

    -- 4.3.4
    contrapose : {A B : Set} → (A → B) → ¬ B → ¬ A
    contrapose f ¬b a = ¬b (f a)

  -- 4.4
  data _+₁_ (A B : Set) : Set where
    left : A → A +₁ B
    right : B → A +₁ B
  infixl 30 _+₁_

  ind-+₁ : {A B : Set} → {P : A +₁ B → Set} → ((x : A) → P(left x)) → ((y : B) → P(right y)) → (z : A +₁ B) → P z
  ind-+₁ pL pR (left x) = pL x
  ind-+₁ pL pR (right y) = pR y

  module +₁-Basic where
    open EmptyBasic

    <_+₁_> : {A B A' B' : Set} → (A → A') → (B → B') → (A +₁ B) → (A' +₁ B')
    < f +₁ g > = ind-+₁ (λ x → left (f x)) (λ y → right (g y))

    +₁-emptyRight : {A B : Set} → is-empty B → A +₁ B → A
    +₁-emptyRight ¬b (left x) = x
    +₁-emptyRight ¬b (right y) = absurd (¬b y)

    +₁-emptyLeft : {A B : Set} → is-empty A → A +₁ B → B
    +₁-emptyLeft ¬a (left x) = absurd (¬a x)
    +₁-emptyLeft ¬a (right y) = y

  -- 4.5
  data Int : Set where
    zeroInt : Int
    posSucc : Nat → Int
    negSucc : Nat → Int

  module IntBasic where
    Int-succ : Int → Int
    Int-succ zeroInt = posSucc zero
    Int-succ (posSucc n) = posSucc (succ n)
    Int-succ (negSucc zero) = zeroInt
    Int-succ (negSucc (succ n)) = negSucc n

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
    add : Int → Int → Int
    add zeroInt m = m
    add m zeroInt = m
    add (posSucc n) (posSucc m) = posSucc (succ (NatBasic.add n m))
    add (posSucc zero) (negSucc zero) = zeroInt
    add (posSucc zero) (negSucc (succ n)) = negSucc n
    add (posSucc (succ n)) (negSucc zero) = posSucc n
    add (posSucc (succ n)) (negSucc (succ m)) = add (posSucc n) (negSucc m)
    add (negSucc zero) (posSucc zero) = zeroInt
    add (negSucc zero) (posSucc (succ n)) = posSucc n
    add (negSucc (succ n)) (posSucc zero) = negSucc n
    add (negSucc (succ n)) (posSucc (succ m)) = add (negSucc n) (posSucc m)
    add (negSucc n) (negSucc m) = negSucc (succ (NatBasic.add n m))

    -- exercise 4.1.b
    neg : Int → Int
    neg zeroInt = zeroInt
    neg (posSucc n) = negSucc n
    neg (negSucc n) = posSucc n

    -- exercise 4.1.c
    mul : Int → Int → Int
    mul zeroInt m = zeroInt
    mul m zeroInt = zeroInt
    mul (posSucc n) (posSucc m) = pred (posSucc (NatBasic.mul (succ n) (succ m)))
    mul (posSucc n) (negSucc m) = Int-succ (negSucc (NatBasic.mul (succ n) (succ m)))
    mul (negSucc n) (posSucc m) = Int-succ (negSucc (NatBasic.mul (succ n) (succ m)))
    mul (negSucc n) (negSucc m) = pred (posSucc (NatBasic.mul (succ n) (succ m)))

  -- 4.6
  record Σ (A : Set) (B : A → Set) : Set where
    constructor pair
    field
      fst : A
      snd : B fst
  
  ind-Σ : {A : Set} → {B : A → Set} → {P : (x : Σ A B) → Set} →
          ((x : A) → (y : B x) → P (pair x y)) →
          (z : Σ A B) → P z
  ind-Σ pXY (pair x y) = pXY x y

  module Σ-Basic where
    pr₁ : {A : Set} → {B : A → Set} → Σ A B → A
    pr₁ (pair x y) = x

    pr₂ : {A : Set} → {B : A → Set} → (p : Σ A B) → B (pr₁ p)
    pr₂ (pair x y) = y

    curry : {A : Set} → {B : A → Set} → {P : Σ A B → Set} →
            ((z : Σ A B) → P z) →
            (x : A) → (y : B x) → P (pair x y)
    curry p x y = p (pair x y)

    uncurry : {A : Set} → {B : A → Set} → {P : Σ A B → Set} →
              ((x : A) → (y : B x) → P (pair x y)) →
              (z : Σ A B) → P z
    uncurry = ind-Σ

  _×_ : (A B : Set) → Set
  A × B = Σ A (λ x → B)

  ind-× : {A B : Set} → {P : A × B → Set} →
          ((x : A) → (y : B) → P (pair x y)) →
          (z : A × B) → P z
  ind-× pXY (pair x y) = pXY x y

  data Bool : Set where
    true false : Bool
  
  ind-Bool : {P : Bool → Set} →
             (pT : P true) → (pF : P false) →
             (b : Bool) → P b
  ind-Bool pT pF true = pT
  ind-Bool pT pF false = pF

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

  _↔_ : Set → Set → Set
  A ↔ B = (A → B) × (B → A)

  module exercise-4-3 where
    open EmptyBasic
    open Σ
    open Σ-Basic

    ¬¬_ : Set → Set
    ¬¬_ A = ¬ ¬ A
    infix 50 ¬¬_

    ex-a-i : {P : Set} → ¬ (P × ¬ P)
    ex-a-i p×¬p = (snd p×¬p) (fst p×¬p)

    ex-a-ii : {P : Set} → ¬ (P ↔ ¬ P)
    ex-a-ii p↔¬p = do
      let ¬p = λ p → (fst p↔¬p) p p
          p = (snd p↔¬p) ¬p
      ¬p p

    ex-b-i : {P : Set} → P → ¬¬ P
    ex-b-i p ¬p = ¬p p
    
    ex-b-ii : {P Q : Set} → (P → Q) → (¬¬ P → ¬¬ Q)
    ex-b-ii p→q ¬¬p ¬q = ¬¬p (λ p → ¬q (p→q p))

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

    ex-c-i : {P : Set} → ¬¬ (¬¬ P → P)
    ex-c-i ¬DNE = ¬DNE (λ ¬¬p → absurd (¬¬p (λ p → ¬DNE (λ _ → p))))

    ex-c-ii : {P Q : Set} → ¬¬ (((P → Q) → P) → P)
    ex-c-ii not-peirce-law =
      not-peirce-law (λ pqpp →
        pqpp (λ p →
          absurd (not-peirce-law (λ _ → p))
        )
      )
    
    ex-c-iii : {P Q : Set} → ¬¬ ((P → Q) +₁ (Q → P))
    ex-c-iii not-dummett-law =
      not-dummett-law (left (λ p → absurd (not-dummett-law (right (λ _ → p)))))

    ex-c-iv : {P : Set} → ¬¬ (P +₁ ¬ P)
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

    ex-d-i : {P : Set} → (P +₁ ¬ P) → (¬¬ P → P)
    ex-d-i (left p) ¬¬p = p
    ex-d-i (right ¬p) ¬¬p = absurd (¬¬p ¬p)

    ex-d-ii : {P Q : Set} → (¬¬(Q → P)) ↔ ((P +₁ ¬ P) → (Q → P))
    ex-d-ii = pair
      (λ ¬¬qp lem q → case lem of λ
        { (left p) → p
        ; (right ¬p) → absurd (¬¬qp (λ qp → ¬p (qp q)))
        })
      (λ lemToQ→P → map lemToQ→P ex-c-iv)

    ex-e-i : {P : Set} → ¬ ¬ ¬ P → ¬ P
    ex-e-i ¬¬¬p p = ¬¬¬p (λ ¬p → ¬p p)

    ex-e-ii : {P Q : Set} → ¬¬(P → ¬¬ Q) → (P → ¬¬ Q)
    ex-e-ii ¬¬p→¬¬q p = do
      p→¬¬q ← ¬¬p→¬¬q
      q ← p→¬¬q p
      pure q

    ex-e-iii : {P Q : Set} → ¬¬((¬¬ P) × (¬¬ Q)) → ¬¬ P × ¬¬ Q
    ex-e-iii ¬¬-pair = pair (¬¬-pair >>= pr₁) (¬¬-pair >>= pr₂)

    ex-f-i : {P Q : Set} → ¬¬(P × Q) ↔ (¬¬ P × ¬¬ Q)
    ex-f-i = pair
      (λ ¬¬pq → pair (map pr₁ ¬¬pq) (map pr₂ ¬¬pq))
      (λ { (pair ¬¬p ¬¬q) → do
        p ← ¬¬p
        q ← ¬¬q
        pure (pair p q)
      })

    ex-f-ii' : {P Q : Set} → ¬ (P +₁ Q) ↔ (¬ P × ¬ Q)
    ex-f-ii' = pair
      (λ ¬p∨q → pair (λ p → ¬p∨q (left p)) (λ q → ¬p∨q (right q)))
      (λ { (pair ¬p _) (left p) → ¬p p ; (pair _ ¬q) (right q) → ¬q q })

    ↔-neg-of-↔ : {P Q : Set} → (P ↔ Q) → (¬ P ↔ ¬ Q)
    ↔-neg-of-↔ (pair p→q q→p) = pair (contrapose q→p) (contrapose p→q)

    ex-f-ii : {P Q : Set} → ¬¬(P +₁ Q) ↔ ¬(¬ P × ¬ Q)
    ex-f-ii = ↔-neg-of-↔ ex-f-ii'

    ex-f-iii : {P Q : Set} → ¬¬(P → Q) ↔ (¬¬ P → ¬¬ Q)
    ex-f-iii = pair
      (_<*>_)
      (λ ¬¬p→¬¬q ¬p→q →
         absurd (¬p→q (λ p →
           absurd (
             ¬¬p→¬¬q (λ ¬p → ¬p p) (λ q → ¬p→q (λ _ → q))
           )
         ))
      )

  -- exercise 4.4
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A
  
  -- a
  ind-List : {A : Set} → {P : List A → Set} →
             (pNil : P nil) →
             ((x : A) (xs : List A) → P xs → P (cons x xs)) →
             (z : List A) → P z
  ind-List pNil pCons nil = pNil
  ind-List pNil pCons (cons x xs) = pCons x xs (ind-List pNil pCons xs)

  module List-Basic where
    -- b
    fold : {A B : Set} → B → (A → B → B) → List A → B
    fold b f nil = b
    fold b f (cons x xs) = f x (fold b f xs)

    -- c
    map : {A B : Set} → (A → B) → List A → List B
    map f nil = nil
    map f (cons x xs) = cons (f x) (map f xs)

    -- d
    length : {A : Set} → List A → Nat
    length nil = zero
    length (cons _ xs) = succ (length xs)

    -- e
    sum : List Nat → Nat
    sum nil = zero
    sum (cons x xs) = NatBasic.add x (sum xs)
    
    product : List Nat → Nat
    product nil = NatBasic.one
    product (cons x xs) = NatBasic.mul x (product xs)

    -- f
    concat : {A : Set} → List A → List A → List A
    concat nil ys = ys
    concat (cons x xs) ys = cons x (concat xs ys)

    -- g
    flatten : {A : Set} → List (List A) → List A
    flatten nil = nil
    flatten (cons xs xss) = concat xs (flatten xss)

    -- h
    reverse : {A : Set} → List A → List A
    reverse = go nil where
      go : {A : Set} → List A → List A → List A
      go acc nil = acc
      go acc (cons x xs) = go (cons x acc) xs
