open import section-2
open import section-3
open import section-4

open import Function.Base using (case_of_)

module _ where
  data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a

  infix 5 _≡_

  ind-≡ : {A : Set} → {a : A} →
          {P : (x : A) → (a ≡ x) → Set} →
          P a refl →
          ((x : A) → (p : a ≡ x) → P x p)
  ind-≡ parefl x refl = parefl

  module ≡-Basic where
    concat : {A : Set} → {x y z : A} →
             (x ≡ y) → (y ≡ z) → (x ≡ z)
    concat refl yz = yz

    _·_ : {A : Set} → {x y z : A} →
          (x ≡ y) → (y ≡ z) → (x ≡ z) 
    _·_ = concat

    infixl 40 _·_

    inverse : {A : Set} → {x y : A} →
             (x ≡ y) → (y ≡ x)
    inverse refl = refl

    _⁻¹ : {A : Set} → {x y : A} →
          (p : x ≡ y) → y ≡ x
    _⁻¹ = inverse

    infix 54 _⁻¹

    assoc : {A : Set} → {x y z w : A} →
            (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
            (p · q) · r ≡ p · (q · r)
    assoc refl p r = refl

    ·-lunit : {A : Set} → {x y : A} →
              (p : x ≡ y) → refl · p ≡ p
    ·-lunit p = refl

    ·-runit : {A : Set} → {x y : A} →
              (p : x ≡ y) → p · refl ≡ p
    ·-runit refl = refl

    ·-linv : {A : Set} → {x y : A} →
             (p : x ≡ y) → p ⁻¹ · p ≡ refl
    ·-linv refl = refl

    ·-rinv : {A : Set} → {x y : A} →
             (p : x ≡ y) → p · p ⁻¹ ≡ refl
    ·-rinv refl = refl

    ap : {A B : Set} → (f : A → B) → {x y : A} → (p : x ≡ y) → f x ≡ f y
    ap f refl = refl

    ap-refl : {A B : Set} → (f : A → B) → (x : A) → ap f {x} refl ≡ refl
    ap-refl f x = refl

    ap-inv : {A B : Set} → (f : A → B) → {x y : A} →
             (p : x ≡ y) → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
    ap-inv f refl = refl

    ap-concat : {A B : Set} → (f : A → B) → {x y z : A} →
                (p : x ≡ y) → (q : y ≡ z) →
                ap f (p · q) ≡ ap f p · ap f q
    ap-concat f refl q = refl
 
    tr : {A : Set} → (B : A → Set) →
         {x y : A} → (p : x ≡ y) →
         B x → B y
    tr B refl b = b

    apd : {A : Set} → {B : A → Set} →
          (f : (a : A) → B a) →
          {x y : A} →
          (p : x ≡ y) →
          tr B p (f x) ≡ f y
    apd f refl = refl

  -- adapted from https://plfa.github.io/Equality/
  module ≡-Reasoning {A : Set} where
    open ≡-Basic

    infix  1 begin_
    infixr 2 step-≡-∣ step-≡-⟩
    infix  3 _∎

    begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
    begin x≡y = x≡y

    step-≡-∣ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
    step-≡-∣ x x≡y = x≡y

    step-≡-⟩ : ∀ (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
    step-≡-⟩ x y≡z x≡y = concat x≡y y≡z

    syntax step-≡-∣ x x≡y      =  x ≡⟨⟩ x≡y
    syntax step-≡-⟩ x y≡z x≡y  =  x ≡⟨ x≡y ⟩ y≡z

    _∎ : ∀ (x : A) → x ≡ x
    x ∎  =  refl

  module ≡-Basic1 where
    open ≡-Basic
    open ≡-Reasoning

    -- 5.5.1
    refl-uniq : {A : Set} → (a : A) → (y : Σ A (λ x → a ≡ x)) →
                pair a refl ≡ y
    refl-uniq a (pair x refl) = refl

    -- exercise 5.1
    distr-inv-concat : {A : Set} → {x y z : A} →
      (p : x ≡ y) → (q : y ≡ z) →
      (p · q) ⁻¹ ≡ q ⁻¹ · p ⁻¹
    distr-inv-concat refl q =
      begin
        (refl · q) ⁻¹
      ≡⟨⟩
        q ⁻¹
      ≡⟨ inverse (·-runit (q ⁻¹)) ⟩
        q ⁻¹ · refl
      ≡⟨⟩
        q ⁻¹ · refl ⁻¹
      ∎

    -- exercise 5.2
    inv-con : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (r : x ≡ z) →
              (p · q ≡ r) → (q ≡ p ⁻¹ · r)
    inv-con refl q r pqr = pqr

    con-inv : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (r : x ≡ z) →
              (p · q ≡ r) → (p ≡ r · q ⁻¹)
    con-inv p refl r pq≡r =
      begin
        p
      ≡⟨ inverse (·-runit p) ⟩
        p · refl
      ≡⟨ pq≡r ⟩
        r
      ≡⟨ inverse (·-runit r) ⟩
        r · refl
      ≡⟨⟩
        r · refl ⁻¹
      ∎

    -- exercise 5.3
    lift : {A : Set} → {B : A → Set} → {a x : A} →
          (p : a ≡ x) → (b : B a) → pair a b ≡ pair x (tr B p b)
    lift refl b = refl

    module exercise-5-4 where
      variable
        A : Set
        a b c d e : A
        p : a ≡ b
        q : b ≡ c
        r : c ≡ d
        s : d ≡ e
      
      α₁ : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
           ((p · q) · r) · s ≡ (p · (q · r)) · s
      α₁ p q r s = ap (λ x → x · s) (assoc p q r)

      α₂ : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
           (p · (q · r)) · s ≡ p · ((q · r) · s)
      α₂ p q r s = assoc p (q · r) s

      α₃ : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
           p · ((q · r) · s) ≡ p · (q · (r · s))
      α₃ p q r s = ap (λ x → p · x) (assoc q r s)

      α₄ : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
           ((p · q) · r) · s ≡ (p · q) · (r · s)
      α₄ p q r s = assoc (p · q) r s

      α₅ : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
           (p · q) · (r · s) ≡ p · (q · (r · s))
      α₅ p q r s = assoc p q (r · s)

      -- exercise 5.4.b
      pentagon : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
                 (α₁ p q r s) · (α₂ p q r s) · (α₃ p q r s) ≡ (α₄ p q r s) · (α₅ p q r s)
      pentagon refl refl refl refl = refl

  module NatEquality where
    open NatBasic public
    open ≡-Basic public
    open NatBasic.Symbolic
    open ≡-Reasoning

    -- 5.6.1
    add-lunit : (n : Nat) → zero + n ≡ n
    add-lunit zero = refl
    add-lunit (succ n) =
      begin
        zero + (succ n)
      ≡⟨⟩
        succ (zero + n)
      ≡⟨ ap succ (add-lunit _) ⟩ 
        succ n
      ∎

    add-runit : (n : Nat) → (add n zero) ≡ n
    add-runit n = refl

    -- 5.6.2
    add-succ-left : (m n : Nat) →
      (succ m) + n ≡ succ (m + n)
    add-succ-left m zero = refl
    add-succ-left m (succ n) =
      begin
        succ m + succ n
      ≡⟨⟩
        succ ((succ m) + n)
      ≡⟨ ap succ (add-succ-left _ _) ⟩
        succ (succ (m + n))
      ∎

    add-succ-right : (m n : Nat) → m + (succ n) ≡ succ (m + n)
    add-succ-right m n = refl

    -- 5.6.3
    add-assoc : (m n k : Nat) → (m + n) + k ≡ m + (n + k)
    add-assoc m n zero = refl
    add-assoc m n (succ k) =
      begin
        (m + n) + (succ k)
      ≡⟨⟩
        succ ((m + n) + k)
      ≡⟨ ap succ (add-assoc m n k) ⟩
        succ (m + (n + k))
      ≡⟨⟩
        m + (n + (succ k))
      ∎
    
    -- 5.6.4
    add-comm : (m n : Nat) → m + n ≡ n + m
    add-comm zero n = add-lunit n
    add-comm (succ m) n =
      begin
        (succ m) + n
      ≡⟨ add-succ-left _ _ ⟩
        succ (m + n)
      ≡⟨ ap succ (add-comm m n) ⟩
        succ (n + m)
      ≡⟨⟩
        n + (succ m)
      ∎

  -- exercise 5.5
  module NatCommSemiring where
    open NatBasic.Symbolic
    open NatEquality
    open ≡-Reasoning

    mul-rzero : (n : Nat) → n * zero ≡ zero
    mul-rzero n = refl

    mul-lzero : (n : Nat) → zero * n ≡ zero
    mul-lzero zero = refl
    mul-lzero (succ n) =
      begin
        zero * (succ n)
      ≡⟨⟩
        zero + (zero * n)
      ≡⟨ add-lunit _ ⟩
        zero * n
      ≡⟨ mul-lzero n ⟩
        zero
      ∎
    
    mul-runit : (n : Nat) → n * one ≡ n
    mul-runit n = refl

    mul-lunit : (n : Nat) → one * n ≡ n
    mul-lunit zero = refl
    mul-lunit (succ n) =
      begin
        one * (succ n)
      ≡⟨⟩
        one + (one * n)
      ≡⟨ ap (λ e → one + e) (mul-lunit _) ⟩
        one + n
      ≡⟨ add-comm one n ⟩
        n + one
      ≡⟨⟩
        succ n
      ∎

    mul-succ-right : (m n : Nat) → m * (succ n) ≡ m + m * n
    mul-succ-right m n = refl

    mul-succ-left : (m n : Nat) → (succ m) * n ≡ (m * n) + n
    mul-succ-left m zero =
      begin
        (succ m) * zero
      ≡⟨⟩
        zero
      ≡⟨ add-runit _ ⟩
        zero + zero
      ≡⟨⟩
        (m * zero) + zero
      ∎
    mul-succ-left m (succ n) =
      begin
        (succ m) * (succ n)
      ≡⟨⟩
        (succ m) + ((succ m) * n)
      ≡⟨ ap (λ e → (succ m) + e) (mul-succ-left m n) ⟩
        (succ m) + ((m * n) + n)
      ≡⟨ inverse (add-assoc (succ m) (m * n) n) ⟩
        ((succ m) + (m * n)) + n
      ≡⟨ ap (λ e → e + n) (add-succ-left _ _) ⟩
        succ (m + (m * n)) + n
      ≡⟨ add-succ-left _ _ ⟩
        succ ((m + (m * n)) + n)
      ≡⟨⟩
        (m * (succ n)) + (succ n)
      ∎

    -- exercise 5.5.b
    mul-comm : (m n : Nat) → m * n ≡ n * m
    mul-comm m zero =
      begin
        m * zero
      ≡⟨⟩
        zero
      ≡⟨ inverse (mul-lzero m) ⟩
        zero * m
      ∎
    mul-comm m (succ n) =
      begin
        m * (succ n)
      ≡⟨ mul-succ-right m n ⟩
        m + (m * n)
      ≡⟨ ap (λ e → m + e) (mul-comm m n) ⟩
        m + (n * m)
      ≡⟨ add-comm m (n * m) ⟩
        (n * m) + m
      ≡⟨ inverse (mul-succ-left n m) ⟩
        (succ n) * m
      ∎

    -- exercise 5.5.c
    mul-ldistr : (m n k : Nat) → m * (n + k) ≡ (m * n) + (m * k)
    mul-ldistr m n zero =
      begin
        m * (n + zero)
      ≡⟨⟩
        m * n
      ≡⟨ add-runit _ ⟩
        (m * n) + zero
      ≡⟨⟩
        (m * n) + (m * zero)
      ∎
    mul-ldistr m n (succ k) =
      begin
        m * (n + (succ k))
      ≡⟨⟩
        m * (succ (n + k))
      ≡⟨⟩
        m + (m * (n + k))
      ≡⟨ ap (λ e → m + e) (mul-ldistr m n k) ⟩
        m + ((m * n) + (m * k))
      ≡⟨ inverse (add-assoc m (m * n) (m * k)) ⟩
        (m + (m * n)) + (m * k)
      ≡⟨ ap (λ e → e + (m * k)) (add-comm m (m * n)) ⟩
        ((m * n) + m) + (m * k)
      ≡⟨ add-assoc (m * n) m (m * k) ⟩
        (m * n) + (m + (m * k))
      ≡⟨⟩
        (m * n) + (m * (succ k))
      ∎
    
    mul-rdistr : (m n k : Nat) → (m + n) * k ≡ (m * k) + (n * k)
    mul-rdistr m n k =
      begin
        (m + n) * k
      ≡⟨ mul-comm (m + n) k ⟩
        k * (m + n)
      ≡⟨ mul-ldistr k m n ⟩
        (k * m) + (k * n)
      ≡⟨ ap (λ e → e + (k * n)) (mul-comm k m) ⟩
        (m * k) + (k * n)
      ≡⟨ ap (λ e → (m * k) + e) (mul-comm k n) ⟩
        (m * k) + (n * k)
      ∎

    -- exercise 5.5.d
    mul-assoc : (m n k : Nat) → (m * n) * k ≡ m * (n * k)
    mul-assoc m n zero =
      begin
        (m * n) * zero
      ≡⟨⟩
        zero
      ≡⟨⟩
        m * zero
      ≡⟨⟩
        m * (n * zero)
      ∎
    mul-assoc m n (succ k) =
      begin
        (m * n) * (succ k)
      ≡⟨⟩
        (m * n) + ((m * n) * k)
      ≡⟨ ap (λ e → (m * n) + e) (mul-assoc m n k) ⟩
        (m * n) + (m * (n * k))
      ≡⟨ inverse (mul-ldistr m n (n * k)) ⟩
        m * (n + n * k)
      ≡⟨⟩
        m * (n * (succ k))
      ∎

  module IntEquality where
    open IntBasic public
    open ≡-Basic public
    open ≡-Reasoning

    -- exercise 5.6
    Int-succ-pred : (x : Int) → Int-succ (pred x) ≡ x
    Int-succ-pred x = {!   !}

    Int-pred-succ : (x : Int) → pred (Int-succ x) ≡ x
    Int-pred-succ x = {!   !}

    -- exercise 5.7
    module IntAddAbGroup where

    -- exercise 5.8
    module IntCommRing where
