module _ where
  open import section-5 public
  
  Eq-Nat : (x y : Nat) → Set
  Eq-Nat zero zero = Unit
  Eq-Nat zero (succ y) = Empty
  Eq-Nat (succ x) zero = Empty
  Eq-Nat (succ x) (succ y) = Eq-Nat x y

  module Eq-Nat where
    open ≡-Basic

    -- 6.3.2
    Eq-Nat-refl : (n : Nat) → Eq-Nat n n
    Eq-Nat-refl zero = unit
    Eq-Nat-refl (succ n) = Eq-Nat-refl n

    -- 6.3.3
    eq-then-obseq : (x y : Nat) → (x ≡ y) → Eq-Nat x y
    eq-then-obseq x y eq = ≡-Basic.tr (λ e → Eq-Nat x e) eq (Eq-Nat-refl x)

    obseq-then-eq : (x y : Nat) → Eq-Nat x y → (x ≡ y)
    obseq-then-eq zero zero _ = refl
    obseq-then-eq zero (succ y) bot = EmptyBasic.absurd bot
    obseq-then-eq (succ x) zero bot = EmptyBasic.absurd bot
    obseq-then-eq (succ x) (succ y) eq = ap succ (obseq-then-eq x y eq)

    Nat-≡-biimpl-Eq-Nat : (x y : Nat) → ((x ≡ y) ↔ Eq-Nat x y)
    Nat-≡-biimpl-Eq-Nat x y =
      pair (eq-then-obseq x y) (obseq-then-eq x y)

  module Nat-EqualityThroughEq-Nat where
    open NatCommSemiring public
    open Eq-Nat public
    open EmptyBasic
    open NatBasic.Symbolic
    open ≡-Reasoning

    -- 6.4.1
    succ-inj : (x y : Nat) → (x ≡ y) ↔ (succ x ≡ succ y)
    succ-inj x y = pair
      (λ eq → ap succ eq)
      (λ succeq → obseq-then-eq x y (eq-then-obseq (succ x) (succ y) succeq))

    -- 6.4.2
    zero-neq-succ : (x : Nat) → ¬ (zero ≡ succ x)
    zero-neq-succ x zero-eq-succx = eq-then-obseq zero (succ x) zero-eq-succx

    -- exercise 6.1.a
    add-inj : (m n k : Nat) → (m ≡ n) ↔ (m + k ≡ n + k)
    add-inj m n k = pair
      (λ eq → ap (λ x → x + k) eq)
      (f k)
        where
        f : (k : Nat) → (m + k ≡ n + k) → (m ≡ n)
        f zero eq = eq
        f (succ k) eq = f k ((succ-inj (m + k) (n + k)).Σ.snd eq)

    mul-inj : (m n k : Nat) → (m ≡ n) ↔ (m * succ k ≡ n * succ k)
    mul-inj m n k = pair
      (λ eq → ap (λ x → x * succ k) eq)
      (f m n k)
        where
        f : (m n k : Nat) → (m * succ k ≡ n * succ k) → (m ≡ n)
        f m n zero eq = eq
        f zero zero (succ k) eq = refl
        f zero (succ n) (succ k) eq =
          let
            zero-eq-succ =
              begin
                zero                       ≡⟨ inverse (mul-lzero (succ (succ k))) ⟩
                zero * succ (succ k)       ≡⟨ eq ⟩
                succ n * succ (succ k)     ≡⟨⟩
                succ n + succ n * succ k   ≡⟨ add-succ-left _ _ ⟩
                succ (n + succ n * succ k)
              ∎
          in
            absurd (zero-neq-succ (n + succ n * succ k) zero-eq-succ)
        f (succ m) zero (succ k) eq =
          let
            zero-eq-succ =
              begin
                zero                       ≡⟨ inverse (mul-lzero (succ (succ k))) ⟩
                zero * succ (succ k)       ≡⟨ inverse eq ⟩
                succ m * succ (succ k)     ≡⟨⟩
                succ m + succ m * succ k   ≡⟨ add-succ-left _ _ ⟩
                succ (m + succ m * succ k)
              ∎
          in
            absurd (zero-neq-succ (m + succ m * succ k) zero-eq-succ)
        f (succ m) (succ n) (succ k) eq =
          let
            eq' =
              begin
                m * succ (succ k) + succ (succ k)   ≡⟨ inverse (mul-succ-left m (succ (succ k))) ⟩
                succ m * succ (succ k)              ≡⟨ eq ⟩
                succ n * succ (succ k)              ≡⟨ mul-succ-left n (succ (succ k)) ⟩
                n * succ (succ k) + succ (succ k)
              ∎
            eq'' = (add-inj (m * succ (succ k)) (n * succ (succ k)) (succ (succ k))).Σ.snd eq'
          in
            ap succ (f m n (succ k) eq'')

    -- exercise 6.1.b
    sum-eq-zero-iff-both-zero : (m n : Nat) → (m + n ≡ zero) ↔ ((m ≡ zero) × (n ≡ zero))
    sum-eq-zero-iff-both-zero m n = pair (forward m n) (λ { (pair refl refl) → refl })
      where
      forward : (m n : Nat) → (m + n ≡ zero) → ((m ≡ zero) × (n ≡ zero))
      forward zero zero eq = pair refl refl
      forward (succ m) zero eq = absurd (zero-neq-succ m (inverse eq))
      forward m (succ n) eq = absurd (zero-neq-succ (m + n) (inverse eq))

    product-eq-zero-iff-some-zero : (m n : Nat) → (m * n ≡ zero) ↔ ((m ≡ zero) +₁ (n ≡ zero))
    product-eq-zero-iff-some-zero m n = pair (forward m n) (λ { (left refl) → mul-lzero n ; (right refl) → mul-rzero m })
      where
      forward : (m n : Nat) → (m * n ≡ zero) → ((m ≡ zero) +₁ (n ≡ zero))
      forward m zero eq = right refl
      forward zero n eq = left refl
      forward (succ m) (succ n) eq =
        let
          eq' =
            begin
              zero                   ≡⟨ inverse eq ⟩
              succ m * succ n        ≡⟨⟩
              succ m + succ m * n    ≡⟨ add-succ-left _ _ ⟩
              succ (m + succ m * n)
            ∎
        in
          absurd (zero-neq-succ (m + succ m * n) eq')

    product-eq-one-iff-both-one : (m n : Nat) → (m * n ≡ one) ↔ ((m ≡ one) × (n ≡ one))
    product-eq-one-iff-both-one m n = pair (forward m n) (λ { (pair refl refl) → refl })
      where
      forward : (m n : Nat) → (m * n ≡ one) → ((m ≡ one) × (n ≡ one))
      forward zero zero eq = absurd (zero-neq-succ zero eq)
      forward (succ m) zero eq = absurd (zero-neq-succ zero eq)
      forward zero (succ n) eq = absurd (zero-neq-succ zero (inverse (mul-lzero (succ n)) · eq))
      forward (succ zero) (succ zero) _ = pair refl refl
      forward (succ (succ m)) (succ n) eq =
        let
          eq1 =
            begin
              succ (succ m) * succ n               ≡⟨⟩
              succ (succ m) + succ (succ m) * n    ≡⟨ add-succ-left (succ m) (succ (succ m) * n) ⟩
              succ (succ m + succ (succ m) * n)    ≡⟨ ap succ (add-succ-left m (succ (succ m) * n)) ⟩
              succ (succ (m + succ (succ m) * n))
            ∎
          eq2 =
            begin
              succ (succ (m + succ (succ m) * n))  ≡⟨ inverse eq1 ⟩
              succ (succ m) * succ n               ≡⟨ eq ⟩
              succ zero
            ∎
          eq3 = (succ-inj _ zero).Σ.snd eq2
        in absurd (zero-neq-succ _ (inverse eq3))
      forward (succ m) (succ (succ n)) eq =
        let
          eq1 =
            begin
              succ m * succ (succ n)               ≡⟨ mul-succ-left m (succ (succ n)) ⟩
              m * succ (succ n) + succ (succ n)    ≡⟨⟩
              succ (succ (m * succ (succ n) + n))
            ∎
          eq2 =
            begin
              succ (succ (m * succ (succ n) + n))  ≡⟨ inverse eq1 ⟩
              succ m * succ (succ n)               ≡⟨ eq ⟩
              succ zero
            ∎
          eq3 = (succ-inj _ zero).Σ.snd eq2
        in absurd (zero-neq-succ _ (inverse eq3))

    -- exercise 6.1.c
    self-neq-add-succ : (m n : Nat) → ¬ (m ≡ m + succ n)
    self-neq-add-succ m n eq =
      let
        eq1 = begin
          zero + m     ≡⟨ add-comm zero m ⟩
          m + zero     ≡⟨⟩
          m            ≡⟨ eq ⟩
          m + succ n   ≡⟨ add-comm m (succ n) ⟩
          succ n + m   ∎
        eq2 = (add-inj zero (succ n) m).Σ.snd eq1
      in
        absurd (zero-neq-succ _ eq2)

    self-succ-neq-mul-succ-succ : (m n : Nat) → ¬ (succ m ≡ succ m * succ (succ n))
    self-succ-neq-mul-succ-succ m n eq =
      let
        eq1 = begin
          one * succ m              ≡⟨ mul-succ-left zero (succ m) ⟩
          zero * succ m + succ m    ≡⟨ ap (λ e → e + succ m) (mul-lzero (succ m)) ⟩
          zero + succ m             ≡⟨ add-lunit (succ m) ⟩
          succ m                    ≡⟨ eq ⟩
          succ m * succ (succ n)    ≡⟨ mul-comm (succ m) _ ⟩
          succ (succ n) * succ m    ∎
        eq2 = (mul-inj one (succ (succ n)) m).Σ.snd eq1
        eq3 = (succ-inj zero (succ n)).Σ.snd eq2
      in
        absurd (zero-neq-succ _ eq3)

  Eq-Bool : (x y : Bool) → Set
  Eq-Bool false false = Unit
  Eq-Bool false true = Empty
  Eq-Bool true false = Empty
  Eq-Bool true true = Unit

  -- exercise 6.2
  module Eq-Bool where
    open BoolBasic
    open EmptyBasic
    open ≡-Basic

    Bool-≡-refl : (x : Bool) → Eq-Bool x x
    Bool-≡-refl false = unit
    Bool-≡-refl true = unit

    Bool-≡-biimpl-Eq-Bool : (x y : Bool) → ((x ≡ y) ↔ Eq-Bool x y)
    Bool-≡-biimpl-Eq-Bool x y = pair (forward x y) (backward x y)
      where
      forward : (x y : Bool) → (x ≡ y) → Eq-Bool x y
      forward x y refl = Bool-≡-refl x

      backward : (x y : Bool) → Eq-Bool x y → (x ≡ y)
      backward false false _ = refl
      backward false true bot = EmptyBasic.absurd bot
      backward true false bot = EmptyBasic.absurd bot
      backward true true _ = refl

    self-neq-neg-bool : (x : Bool) → ¬ (x ≡ neg-bool x)
    self-neq-neg-bool false eq = (Bool-≡-biimpl-Eq-Bool false true).Σ.fst eq
    self-neq-neg-bool true eq = (Bool-≡-biimpl-Eq-Bool true false).Σ.fst eq

    false-neq-true : ¬ (false ≡ true)
    false-neq-true eq = self-neq-neg-bool false eq

  Leq-Nat : (x y : Nat) → Set
  Leq-Nat zero y = Unit
  Leq-Nat (succ x) zero = Empty
  Leq-Nat (succ x) (succ y) = Leq-Nat x y

  module Leq-Nat where
    module Symbolic where
      _≤_ : Nat → Nat → Set
      _≤_ = Leq-Nat
      infix 30 _≤_  
    open Symbolic
    open ≡-Reasoning
    open NatCommSemiring
    open NatBasic.Symbolic

    Leq-Nat-refl : (n : Nat) → n ≤ n
    Leq-Nat-refl zero = unit
    Leq-Nat-refl (succ n) = Leq-Nat-refl n

    Leq-Nat-antisymm : (x y : Nat) → (x ≤ y) → (y ≤ x) → (x ≡ y)
    Leq-Nat-antisymm zero zero _ _ = refl
    Leq-Nat-antisymm zero (succ y) _ bot = EmptyBasic.absurd bot
    Leq-Nat-antisymm (succ x) zero bot _ = EmptyBasic.absurd bot
    Leq-Nat-antisymm (succ x) (succ y) x≤y y≤x = ap succ (Leq-Nat-antisymm x y x≤y y≤x)

    Leq-Nat-trans : (x y z : Nat) → (x ≤ y) → (y ≤ z) → (x ≤ z)
    Leq-Nat-trans zero     zero     zero     _   _   = unit
    Leq-Nat-trans zero     zero     (succ z) _   _   = unit
    Leq-Nat-trans zero     (succ y) (succ z) x≤y y≤z = Leq-Nat-trans zero y z x≤y y≤z
    Leq-Nat-trans (succ x) zero     _        bot _   = EmptyBasic.absurd bot
    Leq-Nat-trans _        (succ y) zero     _   bot = EmptyBasic.absurd bot
    Leq-Nat-trans (succ x) (succ y) (succ z) x≤y y≤z = Leq-Nat-trans x y z x≤y y≤z

    Leq-Nat-total : (x y : Nat) → (x ≤ y) +₁ (y ≤ x)
    Leq-Nat-total zero y = left unit
    Leq-Nat-total (succ x) zero = right unit
    Leq-Nat-total (succ x) (succ y) = Leq-Nat-total x y

    Leq-Nat-self-succ : (x : Nat) → (x ≤ succ x)
    Leq-Nat-self-succ zero = unit
    Leq-Nat-self-succ (succ x) = Leq-Nat-self-succ x

    Leq-Nat-self-add : (x k : Nat) → (x ≤ x + k)
    Leq-Nat-self-add x zero = Leq-Nat-refl x
    Leq-Nat-self-add x (succ k) = Leq-Nat-trans x (x + k) (x + succ k) (Leq-Nat-self-add x k) (Leq-Nat-self-succ (x + k))

    Leq-Nat-biimpl-exists-diff : (x y : Nat) → (x ≤ y) ↔ (Σ Nat (λ k → x + k ≡ y))
    Leq-Nat-biimpl-exists-diff x y = pair (forward x y) (backward x y)
      where
      forward : (x y : Nat) → (x ≤ y) → Σ Nat (λ k → x + k ≡ y)
      forward zero zero     _   = pair zero refl
      forward zero (succ y) _   = pair (succ y) (add-lunit (succ y)) 
      forward (succ x) zero bot = EmptyBasic.absurd bot
      forward (succ x) (succ y) succx≤succy =
        let (pair k eq) = forward x y succx≤succy
            eq' = begin
              (succ x) + k    ≡⟨ add-succ-left x k ⟩
              succ (x + k)    ≡⟨ ap succ eq ⟩
              succ y          ∎
        in (pair k eq')

      backward : (x y : Nat) → Σ Nat (λ k → x + k ≡ y) → (x ≤ y)
      backward x y (pair k refl) = Leq-Nat-self-add x k

    Leq-Nat-biimpl-add-right : (x y k : Nat) → (x ≤ y) ↔ (x + k ≤ y + k)
    Leq-Nat-biimpl-add-right x y k = pair (forward x y k) (backward x y k)
      where
      forward : (x y k : Nat) → (x ≤ y) → (x + k ≤ y + k)
      forward x y zero x≤y = x≤y
      forward x y (succ k) x≤y = forward x y k x≤y

      backward : (x y k : Nat) → (x + k ≤ y + k) → (x ≤ y)
      backward x y zero x+k≤y+k = x+k≤y+k
      backward x y (succ k) x+succk≤y+succk = backward x y k x+succk≤y+succk

    Leq-Nat-biimpl-add-left : (x y k : Nat) → (x ≤ y) ↔ (k + x ≤ k + y)
    Leq-Nat-biimpl-add-left x y k = tr2 (λ e1 e2 → (x ≤ y) ↔ (e1 ≤ e2)) (add-comm x k) (add-comm y k) (Leq-Nat-biimpl-add-right x y k)

    Leq-Nat-add : (a b c d : Nat) → (a ≤ b) → (c ≤ d) → (a + c ≤ b + d)
    Leq-Nat-add a b c d a≤b c≤d =
      let (pair b-a eqba) = (Leq-Nat-biimpl-exists-diff a b).Σ.fst a≤b
          (pair d-c eqdc) = (Leq-Nat-biimpl-exists-diff c d).Σ.fst c≤d
          eq1 = begin
            a + c + (b-a + d-c)  ≡⟨ add-unassoc (a + c) b-a d-c ⟩
            a + c + b-a + d-c    ≡⟨ ap (λ e → e + d-c) (add-add-rcomm a c b-a) ⟩
            a + b-a + c + d-c    ≡⟨ ap (λ e → e + c + d-c) eqba ⟩
            b + c + d-c          ≡⟨ add-assoc b c _ ⟩
            b + (c + d-c)        ≡⟨ ap (λ e → b + e) eqdc ⟩
            b + d                ∎
      in (Leq-Nat-biimpl-exists-diff (a + c) (b + d)).Σ.snd (pair (b-a + d-c) eq1)

    Let-Nat-biimpl-mul : (x y k : Nat) → (x ≤ y) ↔ (x * succ k ≤ y * succ k)
    Let-Nat-biimpl-mul x y k = pair (forward' x y (succ k)) (backward x y k)
      where
      forward' : (x y k : Nat) → (x ≤ y) → (x * k ≤ y * k)
      forward' x y k x≤y =
        let (pair y-x eq) = (Leq-Nat-biimpl-exists-diff x y).Σ.fst x≤y
            eq' = begin
              y * k              ≡⟨ ap (λ e → e * k) (inverse eq) ⟩
              (x + y-x) * k      ≡⟨ mul-rdistr x y-x k ⟩
              x * k + y-x * k    ∎
        in (Leq-Nat-biimpl-exists-diff (x * k) (y * k)).Σ.snd (pair (y-x * k) (inverse eq'))

      backward : (x y k : Nat) → (x * succ k ≤ y * succ k) → (x ≤ y)
      backward zero     zero     _ _   = unit
      backward zero     (succ y) _ _   = unit 
      backward (succ x) zero     k leq =
        EmptyBasic.absurd (tr2 (λ e1 e2 → e1 ≤ e2)
          (add-succ-left x (succ x * k))
          (mul-lzero (succ k)) leq)
      backward (succ x) (succ y) k leq =
        let leq1 : x * succ k + succ k ≤ y * succ k + succ k
            leq1 = tr2 (λ e1 e2 → e1 ≤ e2) (mul-succ-left x (succ k)) (mul-succ-left y (succ k)) leq

            leq2 : x * succ k ≤ y * succ k
            leq2 = (Leq-Nat-biimpl-add-right (x * succ k) (y * succ k) (succ k)).Σ.snd leq1
        in backward x y k leq2

    -- TODO: k ≤ min m n ↔ ((k ≤ m) × (k ≤ n))
    -- TODO: max m n ≤ k ↔ ((m ≤ k) × (n ≤ k))

  Lt-Nat : (x y : Nat) → Set
  Lt-Nat zero zero = Empty
  Lt-Nat zero (succ y) = Unit
  Lt-Nat (succ x) zero = Empty
  Lt-Nat (succ x) (succ y) = Lt-Nat x y

  -- TODO: exercise 6.4

  Nat-dist : (m n : Nat) → Nat
  Nat-dist zero zero = zero
  Nat-dist zero (succ n) = succ n
  Nat-dist (succ m) zero = succ m
  Nat-dist (succ m) (succ n) = Nat-dist m n

  module Nat-dist where
    open NatCommSemiring
    open Leq-Nat

    -- TODO: exercise 6.5

  Int-abs : (x : Int) → Nat
  Int-abs zeroInt = zero
  Int-abs (posSucc x) = succ x
  Int-abs (negSucc x) = succ x

  module Int-abs where
    open IntEquality.IntCommRing
    open Leq-Nat

    -- TODO: (x = zerInt) ↔ (Int-abs x = zero)
    -- TODO: Int-abs (x + y) ≤ Int-abs x + Int-abs y
    -- TODO: Int-abs (x * y) = Int-abs x * Int-abs y
