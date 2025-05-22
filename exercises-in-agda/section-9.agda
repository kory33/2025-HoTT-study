open import Function.Base using (case_of_)

module _ where
  open import section-8 public

  -- 9.1.2
  Homotopy : {A : Set} → {B : (x : A) → Set} → (f g : (x : A) → B x) → Set
  Homotopy {A} f g = (x : A) → f x ≡ g x

  module Homotopy where
    open ≡-Basic

    module Symbolic where
      _~_ : {A : Set} → {B : (x : A) → Set} → (f g : (x : A) → B x) → Set
      f ~ g = Homotopy f g

      infixl 5 _~_
    open Symbolic

    -- 9.1.3
    module _ where
      open BoolBasic
      neg-neg-bool : neg-bool ∘ neg-bool ~ id
      neg-neg-bool true = refl
      neg-neg-bool false = refl

    -- 9.1.5 + 9.1.6
    module _ where
      private variable
        A : Set
        B : (x : A) → Set

      htpy-refl    : (f : (x : A) → B x)     → f ~ f
      htpy-refl f x = refl

      htpy-inverse : (f g : (x : A) → B x)   → f ~ g → g ~ f
      htpy-inverse f g H x = inverse (H x)

      htpy-concat  : (f g h : (x : A) → B x) → f ~ g → g ~ h → f ~ h
      htpy-concat f g h H1 H2 x = (H1 x) · (H2 x)

      htpy-eq-refl : (f : (x : A) → B x) → {g : (x : A) → B x} → (f ≡ g) → f ~ g
      htpy-eq-refl f {g} refl = htpy-refl f

      module HomotopyGroupoidSymbolic where
        _·ₕₜₚ_ : {f g h : (x : A) → B x} → f ~ g → g ~ h → f ~ h
        H ·ₕₜₚ G = htpy-concat _ _ _ H G

        infixl 40 _·ₕₜₚ_

        _⁻¹ₕₜₚ : {f g : (x : A) → B x} → f ~ g → g ~ f
        H ⁻¹ₕₜₚ = htpy-inverse _ _ H
        infix 54 _⁻¹ₕₜₚ

      open HomotopyGroupoidSymbolic

      private variable
        f g h i : (x : A) → B x

      htpy-assoc : (H : f ~ g) → (K : g ~ h) → (L : h ~ i) → H ·ₕₜₚ K ·ₕₜₚ L ~ H ·ₕₜₚ (K ·ₕₜₚ L)
      htpy-assoc H K L x = assoc (H x) (K x) (L x)

      htpy-unassoc : (H : f ~ g) → (K : g ~ h) → (L : h ~ i) → H ·ₕₜₚ (K ·ₕₜₚ L) ~ H ·ₕₜₚ K ·ₕₜₚ L
      htpy-unassoc H K L = (htpy-assoc H K L) ⁻¹ₕₜₚ

      htpy-lunit : (H : f ~ g) → (htpy-refl f) ·ₕₜₚ H ~ H
      htpy-lunit H x = ·-lunit (H x)

      htpy-runit : (H : f ~ g) → H ·ₕₜₚ (htpy-refl g) ~ H
      htpy-runit H x = ·-runit (H x)

      htpy-linv : (H : f ~ g) → (H ⁻¹ₕₜₚ ·ₕₜₚ H) ~ htpy-refl g
      htpy-linv H x = ·-linv (H x)

      htpy-rinv : (H : f ~ g) → (H ·ₕₜₚ H ⁻¹ₕₜₚ) ~ htpy-refl f
      htpy-rinv H x = ·-rinv (H x)

    -- 9.1.7
    module _ where
      private variable
        A B C : Set

      rwhisker : (h : B → C) → {f g : A → B} → (H : f ~ g) → h ∘ f ~ h ∘ g
      rwhisker h H x = ap h (H x)

      lwhisker : {g h : B → C} → (H : g ~ h) → (f : A → B) → g ∘ f ~ h ∘ f
      lwhisker H f x = H (f x)
  open Homotopy.Symbolic

  module Homotopy-Reasoning where
    open Homotopy.Symbolic public
    open Homotopy.HomotopyGroupoidSymbolic public
    open Homotopy public

    infix  1 begin-htpy_
    infixr 2 step-~-∣ step-~-⟩
    infix  3 _∎-htpy

    begin-htpy_ : {A : Set} → {B : (x : A) → Set} → {f g : (x : A) → B x} → f ~ g → f ~ g
    begin-htpy f~g = f~g

    step-~-∣ : {A : Set} → {B : (x : A) → Set} → (f : (x : A) → B x) → {g : (x : A) → B x} → f ~ g → f ~ g
    step-~-∣ f f~g = f~g

    step-~-⟩ : {A : Set} → {B : (x : A) → Set} → (f : (x : A) → B x) → {g h : (x : A) → B x} → f ~ g → g ~ h → f ~ h
    step-~-⟩ f f~g g~h = f~g ·ₕₜₚ g~h

    syntax step-~-∣ f f~g      =  f ~⟨⟩ f~g
    syntax step-~-⟩ f f~g g~h  =  f ~⟨ f~g ⟩ g~h

    _∎-htpy : {A : Set} → {B : (x : A) → Set} → (f : (x : A) → B x) → f ~ f
    x ∎-htpy  =  htpy-refl x

  module BiInvertibleMaps where
    -- 9.2.1
    module _ where
      Is-sect-of : {A B : Set} → (f : A → B) → (g : B → A) → Set
      Is-sect-of f g = f ∘ g ~ id

      Sect : {A B : Set} → (f : A → B) → Set
      Sect {A} {B} f = Σ (B → A) (Is-sect-of f)

      Is-retr-of : {A B : Set} → (f : A → B) → (g : B → A) → Set
      Is-retr-of f g = g ∘ f ~ id

      Retr : {A B : Set} → (f : A → B) → Set
      Retr {A} {B} f = Σ (B → A) (Is-retr-of f)

      Is-equiv : {A B : Set} → (f : A → B) → Set
      Is-equiv {A} {B} f = Sect f × Retr f
    
  module Equivalence where
    open BiInvertibleMaps public

    module Symbolic where
      open EmptyBasic
      -- \simeq
      _≃_ : (A B : Set) → Set
      A ≃ B = Σ (A → B) (λ f → Is-equiv f)
      infixl 5 _≃_

      -- \nsimeq
      _≄_ : (A B : Set) → Set
      A ≄ B = ¬ (A ≃ B)
      infixl 5 _≄_

    open Symbolic
    open Homotopy
    open Homotopy.Symbolic
    open HomotopyGroupoidSymbolic
    open ≡-Basic

    -- 9.2.3
    ≃-refl : {A : Set} → A ≃ A
    ≃-refl {A} = (id , (id , λ x → refl), (id , λ x → refl))

    ≃-trans : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
    ≃-trans (f , (sf , Sf), (rf , Rf)) (g , (sg , Sg), (rg , Rg)) =
      (g ∘ f , (sf ∘ sg , λ c → (ap g (Sf (sg c)) · (Sg c))) , (rf ∘ rg , λ c → (ap rf (Rg (f c)) · (Rf c))))
    
    module Equivalence-Reasoning where
      infix  1 begin-≃_
      infixr 2 step-≃-∣ step-≃-⟩
      infix  3 _∎-≃

      begin-≃_ : {A B : Set} → (A≃B : A ≃ B) → A ≃ B
      begin-≃ A≃B = A≃B

      step-≃-∣ : (A : Set) → {B : Set} → (A ≃ B) → (A ≃ B)
      step-≃-∣ A A≃B = A≃B

      step-≃-⟩ : (A : Set) → {B C : Set} → (A ≃ B) → (B ≃ C) → (A ≃ C)
      step-≃-⟩ A A≃B B≃C = ≃-trans A≃B B≃C

      syntax step-≃-∣ A A≃B      =  A ≃⟨⟩ A≃B
      syntax step-≃-⟩ A A≃B B≃C  =  A ≃⟨ A≃B ⟩ B≃C

      _∎-≃ : (A : Set) → A ≃ A
      A ∎-≃  =  ≃-refl
    open Equivalence-Reasoning

    -- 9.2.6
    Has-inverse : {A B : Set} → (f : A → B) → Set
    Has-inverse {A} {B} f = Σ (B → A) (λ g → (f ∘ g ~ id) × (g ∘ f ~ id))

    has-inverse-equiv : {A B : Set} → {f : A → B} → Has-inverse f → Is-equiv f
    has-inverse-equiv (g , FG , GF) = ((g , FG), (g , GF))

    -- 9.2.7 (see diagrams/9.2.7.drawio.svg for pictorial proof)
    equiv-has-inverse : {A B : Set} → {f : A → B} → Is-equiv f → Has-inverse f
    equiv-has-inverse {A} {B} {f} ((g , G), (h , H)) =
      (g , G , (lwhisker K f) ·ₕₜₚ H)
        where
        K : g ~ h
        K = (lwhisker H g) ⁻¹ₕₜₚ ·ₕₜₚ (rwhisker h G)

    -- 9.2.8
    ≃-inverse-map : {A B : Set} → A ≃ B → (B → A)
    ≃-inverse-map (f , (g , _), _) = g

    ≃-inverse-map-is-equiv : {A B : Set} → (eqv : A ≃ B) → Is-equiv (≃-inverse-map eqv)
    ≃-inverse-map-is-equiv (f , f-is-equiv@((g , gsect), (g' , g'retr))) =
      ((f , fsect), (f , gsect))
      where
        fsect : Is-sect-of g f
        fsect = (equiv-has-inverse f-is-equiv) .Σ.snd .Σ.snd

    ≃-inverse : {A B : Set} → A ≃ B → B ≃ A
    ≃-inverse {A} {B} eqv = (≃-inverse-map eqv , ≃-inverse-map-is-equiv eqv)

    ≃-comm : {A B : Set} → A ≃ B → B ≃ A
    ≃-comm eqv = ≃-inverse eqv

    -- exercise 9.1
    module EqualityOps where
      open ≡-Reasoning

      private variable
        A : Set
        B : (x : A) → Set
      
      inv-is-equiv : {x y : A} → Is-equiv (λ (p : x ≡ y) → inverse p)
      inv-is-equiv {x} {y} = ((inverse , (λ { refl → refl })), (inverse , (λ { refl → refl })))

      prepend-path-is-equiv : {x y z : A} → (p : x ≡ y) → Is-equiv (λ (q : y ≡ z) → p · q)
      prepend-path-is-equiv {A} {x} {y} {z} p = ((inverseMap , section-eq), (inverseMap , retract-eq))
        where
          inverseMap : (x ≡ z) → (y ≡ z)
          inverseMap r = p ⁻¹ · r

          section-eq : (_·_ p) ∘ inverseMap ~ id
          section-eq q = begin
            p · (p ⁻¹ · q) ≡⟨ unassoc p (p ⁻¹) q ⟩
            p · p ⁻¹ · q   ≡⟨ ap (λ e → e · q) (·-rinv p) ⟩
            refl · q       ≡⟨⟩
            q              ∎

          retract-eq : inverseMap ∘ (_·_ p) ~ id
          retract-eq q = begin
            p ⁻¹ · (p · q) ≡⟨ unassoc (p ⁻¹) p q ⟩
            p ⁻¹ · p · q   ≡⟨ ap (λ e → e · q) (·-linv p) ⟩
            refl · q       ≡⟨⟩
            q              ∎

      concat-swap-is-equiv : {x y z : A} → (q : y ≡ z) → Is-equiv (λ (p : x ≡ y) → p · q)
      concat-swap-is-equiv {A} {x} {y} {z} q = ((inverseMap , section-eq), (inverseMap , retract-eq))
        where
          inverseMap : (x ≡ z) → (x ≡ y)
          inverseMap r = r · q ⁻¹

          section-eq : (λ p → p · q) ∘ inverseMap ~ id
          section-eq refl = begin
            refl · (q ⁻¹) · q   ≡⟨⟩
            q ⁻¹ · q            ≡⟨ ·-linv q ⟩
            refl                ∎

          retract-eq : inverseMap ∘ (λ p → p · q) ~ id
          retract-eq refl = begin
            refl · q · q ⁻¹   ≡⟨⟩
            q · q ⁻¹          ≡⟨ ·-rinv q ⟩
            refl              ∎

      tr-is-equiv : (B : A → Set) → {x y : A} → (p : x ≡ y) → Is-equiv (tr B p)
      tr-is-equiv B {x} {y} p = ((inverseMap , section-eq), (inverseMap , retract-eq))
        where
          inverseMap : B y → B x
          inverseMap = tr B (p ⁻¹)

          section-eq : (tr B p) ∘ inverseMap ~ id
          section-eq by = begin
            (tr B p ∘ inverseMap) by      ≡⟨⟩
            tr B p (tr B (p ⁻¹) by)       ≡⟨ inverse (≡-Basic1.tr-concat (p ⁻¹) _ _) ⟩
            tr B (p ⁻¹ · p) by            ≡⟨ ap (λ e → tr B e by) (·-linv p) ⟩
            tr B refl by                  ≡⟨⟩
            id by                         ∎

          retract-eq : inverseMap ∘ (tr B p) ~ id
          retract-eq by = begin
            (inverseMap ∘ (tr B p)) by    ≡⟨⟩
            tr B (p ⁻¹) (tr B p by)       ≡⟨ inverse (≡-Basic1.tr-concat p _ _) ⟩
            tr B (p · p ⁻¹) by            ≡⟨ ap (λ e → tr B e by) (·-rinv p) ⟩
            tr B refl by                  ≡⟨⟩
            id by                         ∎

    -- exercise 9.2
    module _ where
      open EmptyBasic
      open Eq-Bool
      open ≡-Reasoning

      const-bool-not-equiv : (b : Bool) → ¬ Is-equiv (λ (b' : Bool) → const b b')
      const-bool-not-equiv true ((g , G), _) = false-neq-true (inverse (G false {-- : true ≡ false --}))
      const-bool-not-equiv false ((g , G), _) = false-neq-true (G true)

      Bool-≄-Unit : Bool ≄ Unit
      Bool-≄-Unit (equiv , ((g , G), (h , H))) =
        const-bool-not-equiv
          (h unit)
          (has-inverse-equiv (
            id ,
            (λ b → begin
              (const (h unit) ∘ id) b    ≡⟨⟩
              h unit                     ≡⟨ ap h (UnitEquality.any-units-eq unit (equiv b)) ⟩
              h (equiv b)                ≡⟨ H b ⟩
              id b                       ∎),
            (λ b → begin
              (id ∘ (const (h unit))) b  ≡⟨⟩
              h unit                     ≡⟨ ap h (UnitEquality.any-units-eq unit (equiv b)) ⟩
              h (equiv b)                ≡⟨ H b ⟩
              id b                       ∎)
          ))

      open +₁-Basic
      open EmptyBasic

      Inhabited-≄-Empty : {A : Set} → (a : A) → A ≄ Empty
      Inhabited-≄-Empty a eqv = absurd ((eqv .Σ.fst) a)

      ≃-comm-+₁ : {A B : Set} → A +₁ B ≃ B +₁ A
      ≃-comm-+₁ =
        (swap-+₁ ,
          (has-inverse-equiv (
            swap-+₁ ,
            (λ { (left _) → refl ; (right _) → refl }),
            (λ { (left _) → refl ; (right _) → refl }))))

      ≃-+₁-both : {A B C D : Set} → (A ≃ C) → (B ≃ D) → (A +₁ B ≃ C +₁ D)
      ≃-+₁-both (f , (fs , fS), (fr , fR)) (g , (gs , gS), (gr , gR)) =
        (< f +₁ g > ,
          ((λ { (left c) → left (fs c) ; (right d) → right (gs d) }) , (λ { (left c) → ap left (fS c) ; (right d) → ap right (gS d) })) ,
          ((λ { (left c) → left (fr c) ; (right d) → right (gr d) }) , (λ { (left c) → ap left (fR c) ; (right d) → ap right (gR d) }))
        )

      Empty-≃-lunit : {A : Set} → Empty +₁ A ≃ A
      Empty-≃-lunit =
        (
          (λ { (left emp) → absurd emp ; (right a) → a }),
          (has-inverse-equiv (
            right ,
            (λ a → refl),
            (λ { (left emp) → absurd emp ; (right a) → refl }))))

      Empty-≃-runit : {A : Set} → A +₁ Empty ≃ A
      Empty-≃-runit {A} = begin-≃
        A +₁ Empty     ≃⟨ ≃-comm-+₁ ⟩
        Empty +₁ A     ≃⟨ Empty-≃-lunit ⟩
        A              ∎-≃

      Nat≃+Unit-then-Nat≃ : {A : Set} → (forward : Nat → A +₁ Unit) → Has-inverse forward → Σ (Nat → A) Has-inverse
      Nat≃+Unit-then-Nat≃ {A} forward (backward , Sect , Retr) =
        (forward' , (backward' , forward'∘backward'~id , backward'∘forward'~id))
        where open Lt-Nat.Symbolic
              open Leq-Nat.Symbolic

              pointToEliminate = backward (right unit)

              forward-is-unit-only-at-pointToEliminate : (n : Nat) → (forward n ≡ right unit) → (n ≡ pointToEliminate)
              forward-is-unit-only-at-pointToEliminate n fn≡unit =
                begin
                  n                      ≡⟨ inverse (Retr n) ⟩
                  backward (forward n)   ≡⟨ ap backward (fn≡unit) ⟩
                  backward (right unit)  ≡⟨⟩
                  pointToEliminate       ∎
              
              blackward-left-is-not-pointToEliminate : (a : A) → pointToEliminate ≢ backward (left a)
              blackward-left-is-not-pointToEliminate a pt≡bla =
                let ru≡la = begin
                      (right unit)                     ≡⟨ inverse (Sect (right unit)) ⟩
                      forward (backward (right unit))  ≡⟨ ap forward pt≡bla ⟩
                      forward (backward (left a))      ≡⟨ Sect (left a) ⟩
                      left a                           ∎
                in Eq-Copr.left-neq-right (inverse ru≡la)

              extract-a-from-forward-cases : (n : Nat) → (n≠pt : n ≢ pointToEliminate) → (copr : A +₁ Unit) → (forward n ≡ copr) → A
              extract-a-from-forward-cases n n≠pt =
                ind-+₁ {A} {Unit} {λ copr → forward n ≡ copr → A}
                  (λ a _ → a)
                  (λ { unit eq → absurd (n≠pt (forward-is-unit-only-at-pointToEliminate n eq)) })
              extract-a-from-forward : (n : Nat) → (n ≢ pointToEliminate) → A
              extract-a-from-forward n n≠pt = extract-a-from-forward-cases n n≠pt (forward n) refl

              extract-a-from-forward-eq-forward : (n : Nat) → {n≠pt : n ≢ pointToEliminate} → left (extract-a-from-forward n n≠pt) ≡ forward n
              extract-a-from-forward-eq-forward n {n≠pt} =
                ind-+₁ {A} {Unit} {λ copr → forward n ≡ copr → left (extract-a-from-forward n n≠pt) ≡ forward n}
                  (λ a eq → begin
                    left (extract-a-from-forward n n≠pt)                            ≡⟨⟩
                    left (extract-a-from-forward-cases n n≠pt (forward n) refl)     ≡⟨ ap left (transport-equality-fn (forward n) (extract-a-from-forward-cases n n≠pt) eq) ⟩
                    left (extract-a-from-forward-cases n n≠pt (left a) eq)          ≡⟨⟩
                    left a                                                          ≡⟨ inverse eq ⟩
                    forward n                                                       ∎
                  )
                  (λ { unit eq → absurd (n≠pt (forward-is-unit-only-at-pointToEliminate n eq)) })
                  (forward n) refl
                where
                  transport-equality-fn : {X P : Set} → (x : X) → (depfn : (z : X) → (x ≡ z) → P) → {y : X} → (q : x ≡ y) → depfn x refl ≡ depfn y q
                  transport-equality-fn x d refl = refl

              forward'-cases : (n : Nat) → ((n < pointToEliminate) +₁ (pointToEliminate ≤ n)) → A
              forward'-cases n =
                λ {
                  (left n<pt) →
                    extract-a-from-forward n (Lt-Nat.lt-then-neq n _ n<pt)
                ; (right pt≤n) →
                    extract-a-from-forward (succ n)
                      (≢-inverse
                        (Lt-Nat.lt-then-neq pointToEliminate (succ n)
                          (Lt-Nat.leq-then-lt-succ pointToEliminate n pt≤n)))
                }
              forward' : Nat → A
              forward' n = Lt-Nat.by-comparing-lt-or-geq n pointToEliminate (forward'-cases n)

              backward'-cases : (res : Nat) → ((res ≤ pointToEliminate) +₁ (pointToEliminate < res)) → Nat
              backward'-cases res =
                λ {
                  (left res≤pt) → res
                ; (right pt<res) → NatBasic.predOrZero res
                }
              backward' : A → Nat
              backward' a = let result = backward (left a) in Lt-Nat.by-comparing-leq-or-gt result pointToEliminate (backward'-cases result)

              left∘forward'≡forward-if-<pt : (n : Nat) → (n < pointToEliminate) → (left (forward' n) ≡ forward n)
              left∘forward'≡forward-if-<pt n n<pt = begin
                left (forward' n)                    ≡⟨ ap left (Lt-Nat.by-comparing-lt-or-geq-lt-case n n<pt) ⟩
                left (forward'-cases n (left n<pt))  ≡⟨⟩
                left (extract-a-from-forward n _)    ≡⟨ extract-a-from-forward-eq-forward n ⟩
                forward n                            ∎

              left∘forward'≡forward∘succ-if-≥pt : (n : Nat) → (pointToEliminate ≤ n) → (left (forward' n) ≡ forward (succ n))
              left∘forward'≡forward∘succ-if-≥pt n n≥pt = begin
                left (forward' n)                          ≡⟨ ap left (Lt-Nat.by-comparing-lt-or-geq-geq-case n n≥pt) ⟩
                left (forward'-cases n (right n≥pt))       ≡⟨⟩
                left (extract-a-from-forward (succ n) _)   ≡⟨ extract-a-from-forward-eq-forward (succ n) ⟩
                forward (succ n)                           ∎
              
              backward'≡predOrZero∘backward∘left-if-bla>pt : (a : A) → (pointToEliminate < backward (left a)) → (backward' a ≡ NatBasic.predOrZero (backward (left a)))
              backward'≡predOrZero∘backward∘left-if-bla>pt a bla>pt = begin
                backward' a                              ≡⟨ Lt-Nat.by-comparing-leq-or-gt-gt-case (backward (left a)) bla>pt ⟩
                NatBasic.predOrZero (backward (left a))  ∎

              backward'≡backward∘left-if-bla≤pt : (a : A) → (backward (left a) ≤ pointToEliminate) → (backward' a ≡ backward (left a))
              backward'≡backward∘left-if-bla≤pt a bla≤pt = begin
                backward' a        ≡⟨ Lt-Nat.by-comparing-leq-or-gt-leq-case (backward (left a)) bla≤pt ⟩
                backward (left a)  ∎
              
              backward'<pt-then-backward∘left≤pt : (a : A) → (backward' a < pointToEliminate) → (backward (left a) ≤ pointToEliminate)
              backward'<pt-then-backward∘left≤pt a b'a<pt =
                Lt-Nat.by-comparing-leq-or-gt (backward (left a)) pointToEliminate λ {
                  (left bla≤pt) → bla≤pt
                ; (right bla>pt) → -- this is a contradictory arm: Can we simply the proof with EmptyBasic.absurd?
                    let (predbla , succ-predbla) = Lt-Nat.gt-something-then-exists-pred (backward (left a)) {pointToEliminate} bla>pt
                        b'a≡predOrZero-bla = backward'≡predOrZero∘backward∘left-if-bla>pt a bla>pt
                        predbla<pt  = tr (λ e → e < pointToEliminate) (b'a≡predOrZero-bla · ap NatBasic.predOrZero succ-predbla · NatEquality.predOrZero-succ predbla) b'a<pt
                        spredbla≤pt = (Lt-Nat.lt-biimpl-succ-leq predbla pointToEliminate).Σ.fst predbla<pt
                        bla≤pt      = tr (λ e → e ≤ pointToEliminate) (inverse succ-predbla) spredbla≤pt
                    in bla≤pt
                }
              backward'≥pt-then-backward∘left>pt : (a : A) → (pointToEliminate ≤ backward' a) → (pointToEliminate < backward (left a))
              backward'≥pt-then-backward∘left>pt a b'a≥pt =
                Lt-Nat.by-comparing-leq-or-gt (backward (left a)) pointToEliminate λ {
                  (left bla≤pt) →
                    let b'a≡bla = backward'≡backward∘left-if-bla≤pt a bla≤pt
                        bla≥pt = tr (λ e → pointToEliminate ≤ e) b'a≡bla b'a≥pt
                    in Lt-Nat.leq-and-neq-then-lt pointToEliminate (backward (left a)) bla≥pt (blackward-left-is-not-pointToEliminate a)
                ; (right bla>pt) → bla>pt
                }

              n<pt-then-blf'a≤pt : (n : Nat) → (n < pointToEliminate) → (backward (left (forward' n)) ≤ pointToEliminate)
              n<pt-then-blf'a≤pt n n<pt =
                let lhs≡n = begin
                      backward (left (forward' n))    ≡⟨ ap backward (left∘forward'≡forward-if-<pt n n<pt) ⟩
                      backward (forward n)            ≡⟨ Retr n ⟩
                      n                               ∎
                in Lt-Nat.as-leq (backward (left (forward' n))) pointToEliminate
                    (tr (λ e → e < pointToEliminate) (inverse lhs≡n) n<pt)

              n≥pt-then-blf'a>pt : (n : Nat) → (pointToEliminate ≤ n) → (pointToEliminate < backward (left (forward' n)))
              n≥pt-then-blf'a>pt n n≥pt =
                let rhs≡sn = begin
                      backward (left (forward' n))  ≡⟨ ap backward (left∘forward'≡forward∘succ-if-≥pt n n≥pt) ⟩
                      backward (forward (succ n))   ≡⟨ Retr (succ n) ⟩
                      succ n                        ∎
                in tr (λ e → pointToEliminate < e) (inverse rhs≡sn) (Lt-Nat.leq-then-lt-succ pointToEliminate n n≥pt)

              forward'∘backward'~id : (a : A) → (forward' (backward' a) ≡ a)
              forward'∘backward'~id a =
                Eq-Copr.+₁-left-inj {A} {Unit} (
                  Lt-Nat.by-comparing-lt-or-geq (backward' a) (pointToEliminate) λ {
                    (left b'a<pt) → begin
                      left (forward' (backward' a)) ≡⟨ left∘forward'≡forward-if-<pt (backward' a) b'a<pt ⟩
                      forward (backward' a)         ≡⟨ ap forward (backward'≡backward∘left-if-bla≤pt a (backward'<pt-then-backward∘left≤pt a b'a<pt)) ⟩
                      forward (backward (left a))   ≡⟨ Sect (left a) ⟩
                      left a                        ∎
                  ; (right b'a≥pt) →
                    let bla>pt = backward'≥pt-then-backward∘left>pt a b'a≥pt
                        (pred-bla , succ-pred-bla) = Lt-Nat.gt-something-then-exists-pred (backward (left a)) {pointToEliminate} bla>pt
                    in begin
                      left (forward' (backward' a))                             ≡⟨ left∘forward'≡forward∘succ-if-≥pt (backward' a) b'a≥pt ⟩
                      forward (succ (backward' a))                              ≡⟨ ap (forward ∘ succ) (backward'≡predOrZero∘backward∘left-if-bla>pt a bla>pt) ⟩
                      forward (succ (NatBasic.predOrZero (backward (left a))))  ≡⟨ ap (forward ∘ succ ∘ NatBasic.predOrZero) succ-pred-bla ⟩
                      forward (succ (NatBasic.predOrZero (succ pred-bla)))      ≡⟨ ap (forward ∘ succ) (NatEquality.predOrZero-succ pred-bla) ⟩
                      forward (succ pred-bla)                                   ≡⟨ ap forward (inverse succ-pred-bla) ⟩
                      forward (backward (left a))                               ≡⟨ Sect (left a) ⟩
                      left a                                                    ∎
                  }
                )

              backward'∘forward'~id : (n : Nat) → (backward' (forward' n) ≡ n)
              backward'∘forward'~id n =
                Lt-Nat.by-comparing-lt-or-geq n pointToEliminate λ {
                  (left n<pt) → begin
                    backward' (forward' n)       ≡⟨ backward'≡backward∘left-if-bla≤pt (forward' n) (n<pt-then-blf'a≤pt n n<pt) ⟩
                    backward (left (forward' n)) ≡⟨ ap backward (left∘forward'≡forward-if-<pt n n<pt) ⟩
                    backward (forward n)         ≡⟨ Retr n ⟩
                    n                            ∎
                ; (right n≥pt) → begin
                    backward' (forward' n)                             ≡⟨ backward'≡predOrZero∘backward∘left-if-bla>pt (forward' n) (n≥pt-then-blf'a>pt n n≥pt) ⟩
                    NatBasic.predOrZero (backward (left (forward' n))) ≡⟨ ap (NatBasic.predOrZero ∘ backward) (left∘forward'≡forward∘succ-if-≥pt n n≥pt) ⟩
                    NatBasic.predOrZero (backward (forward (succ n)))  ≡⟨ ap NatBasic.predOrZero (Retr (succ n)) ⟩
                    NatBasic.predOrZero (succ n)                       ≡⟨ NatEquality.predOrZero-succ n ⟩
                    n                                                  ∎
                }


      Nat-≄-Fin : (k : Nat) → Nat ≄ Fin k
      Nat-≄-Fin zero = Inhabited-≄-Empty zero
      Nat-≄-Fin (succ k) (Nat≃Fink+Unit , is-equiv) =
        let (inv , is-inverse) = Nat≃+Unit-then-Nat≃ Nat≃Fink+Unit (equiv-has-inverse is-equiv)
        in Nat-≄-Fin k (inv , has-inverse-equiv is-inverse)

    -- exercise 9.3 (see diagrams/exercise-9.3.drawio.svg for pictorial proof)
    module _ where
      open ≡-Reasoning
      open Homotopy
      open Homotopy.Symbolic
      open Homotopy-Reasoning
      
      is-equiv-preserved-by-homotopy : {A B : Set} → {f g : A → B} → f ~ g → Is-equiv f → Is-equiv g
      is-equiv-preserved-by-homotopy {A} {B} {f} {g} FG ((s , S), (r , R)) =
        ((s , (lwhisker (FG ⁻¹ₕₜₚ) s ·ₕₜₚ S)),
         (r , (rwhisker r (FG ⁻¹ₕₜₚ) ·ₕₜₚ R)))

      homotope-implies-is-equiv-biimpl : {A B : Set} → {f g : A → B} → f ~ g → Is-equiv f ↔ Is-equiv g
      homotope-implies-is-equiv-biimpl {A} {B} {f} {g} FG =
        (is-equiv-preserved-by-homotopy FG , is-equiv-preserved-by-homotopy (FG ⁻¹ₕₜₚ))

      sect-with-retr-is-retr : {A B : Set} → {f : A → B} → {g : B → A} → Is-sect-of f g → (Σ _ (Is-retr-of f)) → Is-retr-of f g
      sect-with-retr-is-retr {A} {B} {f} {g} gsect retr = equiv-has-inverse ((g , gsect), retr) .Σ.snd .Σ.snd

      homotopic-equiv-has-homotopic-inverses : {A B : Set} → {e e' : A → B} → (ee : Is-equiv e) → (ee' : Is-equiv e') → e ~ e' →
                                               ≃-inverse-map (e , ee) ~ ≃-inverse-map (e' , ee')
      homotopic-equiv-has-homotopic-inverses {A} {B} {e} {e'} ((g , seq), retr) ((g' , seq'), _) H =
        begin-htpy
          g               ~⟨⟩
          g ∘ id          ~⟨ rwhisker g (seq' ⁻¹ₕₜₚ) ⟩
          g ∘ (e' ∘ g')   ~⟨⟩
          g ∘ e' ∘ g'     ~⟨ rwhisker g (lwhisker (H ⁻¹ₕₜₚ) g') ⟩
          g ∘ e ∘ g'      ~⟨ lwhisker (sect-with-retr-is-retr seq retr) g' ⟩
          id ∘ g'         ~⟨⟩
          g'              ∎-htpy

    -- exercise 9.4
    module _ where
      open ≡-Reasoning
      open Homotopy
      open Homotopy.Symbolic
      open Homotopy-Reasoning

      variable
        A B X : Set
        h : A → B
        f : A → X
        g : B → X

            

