open import Function.Base using (case_of_)

module _ where
  open import section-09 public

  open Homotopy
  open Homotopy.Symbolic
  open ≡-Basic
  open ≡-Reasoning

  -- definition 10.1.1
  open import Agda.Primitive
  ContractionTo : {i : Level} → {A : Set i} → A → Set i
  ContractionTo {i} {A} a = (x : A) → a ≡ x

  Is-contr : {i : Level} → Set i → Set i
  Is-contr A = Σ-poly A (λ c → ContractionTo c)

  untangle : {A : Set} → ((c , C) : Is-contr A) → ContractionTo c
  untangle (c , C) a = (C c)⁻¹ · (C a)

  untangled-contr-at-centre : {A : Set} → (contr@(c , C) : Is-contr A) → (untangle contr) c ≡ refl
  untangled-contr-at-centre (c , C) = ·-linv (C c)

  recenter-contraction-at : {A : Set} → (a : A) → Is-contr A → ContractionTo a
  recenter-contraction-at {A} a (c , C) = λ x → (C a)⁻¹ · (C x)

  two-points-eq-in-contr-type : {A : Set} → Is-contr A → (x y : A) → x ≡ y
  two-points-eq-in-contr-type (a , C) x y = (C x)⁻¹ · (C y)

  -- remark 10.1.2
  contraction-to : {A : Set} → (c : A) → Set
  contraction-to c = const c ~ id

  -- example 10.1.3
  Unit-Is-contr : Is-contr Unit
  Unit-Is-contr = (unit , Unit-ind { λ (u : Unit) → unit ≡ u } refl)

  -- theorem 10.1.4
  identity-with-an-endpoint-fixed-Is-contr : {A : Set} → (a : A) → Is-contr (Σ A (λ x → a ≡ x))
  identity-with-an-endpoint-fixed-Is-contr a =
    ((a , refl) , λ pt → ≡-Basic1.refl-uniq a pt)

  -- definition 10.2.1
  ev-pt : {A : Set} → {B : (x : A) → Set} → (a : A) → (f : (x : A) → B x) → B a
  ev-pt a f = f a

  open Equivalence
  singleton-induction-at : {A : Set} → (a : A) → Set₁
  singleton-induction-at {A} a = (B : A → Set) → Sect (ev-pt {A} {B} a)

  -- theorem 10.2.3 (This is stronger than 10.2.3 in the book: a : A is arbitrary with this definition)
  contr-then-sing-ind-at : {A : Set} → (a : A) → Is-contr A → singleton-induction-at a
  contr-then-sing-ind-at {A} a contr =
    λ B →
      let
        recenteredC = (a , recenter-contraction-at a contr)
        C = untangle recenteredC
        ind-sing-a : B a → (x : A) → B x
        ind-sing-a b x = tr B (C x) b
        comp-sing-a : ev-pt a ∘ ind-sing-a ~ id
        comp-sing-a = λ b → begin
          (ev-pt a ∘ ind-sing-a) b ≡⟨⟩
          tr B (C a) b             ≡⟨ ap (λ t → tr B t b) (untangled-contr-at-centre recenteredC) ⟩
          tr B refl b              ≡⟨⟩
          b                        ≡⟨⟩
          id b                     ∎
      in
        (ind-sing-a , comp-sing-a)

  sing-ind-then-contr : {A : Set} → (a : A) → singleton-induction-at a → Is-contr A
  sing-ind-then-contr a ind = (a , λ x → Σ.fst (ind (λ x → a ≡ x)) refl x)

  is-contr-biimpl-sing-ind-at : {A : Set} → (a : A) → (Is-contr A) ↔-poly (singleton-induction-at a)
  is-contr-biimpl-sing-ind-at {A} a = (contr-then-sing-ind-at a , sing-ind-then-contr a)

  -- definition 10.3.1
  fib : {A B : Set} → (f : A → B) → (b : B) → Set
  fib {A} {B} f b = Σ A (λ a → f a ≡ b)

  -- definition 10.3.2
  Eq-fib : {A B : Set} → (f : A → B) → {y : B} → fib f y → fib f y → Set
  Eq-fib f (x , p) (x' , p') = Σ (x ≡ x') (λ α → p ≡ (ap f α) · p')

  Eq-fib-refl : {A B : Set} → (f : A → B) → {y : B} → (x : fib f y) → Eq-fib f x x
  Eq-fib-refl f (x , p) = (refl , refl)

  Eq-fib-from-identity : {A B : Set} → (f : A → B) → {y : B} →
                         {x x' : fib f y} → (p : x ≡ x') → Eq-fib f x x'
  Eq-fib-from-identity f {y} {x} {.x} refl = Eq-fib-refl f x

  open Equivalence

  identity-from-Eq-fib : {A B : Set} → (f : A → B) → {y : B} → (x x' : fib f y) →
    Eq-fib f x x' → x ≡ x'
  identity-from-Eq-fib f {y} (x , α) (x' , α') (refl , refl) = refl

  -- proposition 10.3.3
  Eq-fib-from-identity-is-equiv : {A B : Set} → (f : A → B) → {y : B} → {x x' : fib f y} →
                                  Is-equiv (Eq-fib-from-identity f {y} {x} {x'})
  Eq-fib-from-identity-is-equiv f {y} {xα@(x , α)} {x'} =
    has-inverse-equiv (identity-from-Eq-fib f xα x' , rinverse , linverse)
    where
      rinverse : (Eq-fib-from-identity f) ∘ (identity-from-Eq-fib f xα x') ~ id
      rinverse = by-inductions x'
        where
          by-inductions : (x'' : fib f y) → (p : Eq-fib f xα x'') → (Eq-fib-from-identity f (identity-from-Eq-fib f xα x'' p)) ≡ p
          by-inductions (x' , α') (refl , refl) = refl
      linverse : (identity-from-Eq-fib f xα x') ∘ (Eq-fib-from-identity f {y} {xα} {x'}) ~ id
      linverse refl = refl

  open Equivalence.Symbolic
  fib-identity-equiv-to-eq-fib : {A B : Set} → (f : A → B) → {y : B} → {x x' : fib f y} →
                                 (x ≡ x') ≃ Eq-fib f x x'
  fib-identity-equiv-to-eq-fib {A} {B} f {y} {x} {x'} =
    (Eq-fib-from-identity f , Eq-fib-from-identity-is-equiv f)

  -- definition 10.3.4
  Is-contr-fn : {A B : Set} → (f : A → B) → Set
  Is-contr-fn {A} {B} f = (b : B) → Is-contr (fib f b)

  open Σ

  -- theorem 10.3.5
  contr-fn-then-equiv : {A B : Set} → {f : A → B} → Is-contr-fn f → Is-equiv f
  contr-fn-then-equiv {A} {B} {f} contr =
    let
      gG : (y : B) → fib f y
      gG y = fst (contr y)
      g : B → A
      g y = fst (gG y)
      G : (y : B) → f (g y) ≡ y
      G y = snd (gG y)

      linverse : g ∘ f ~ id
      linverse x = ap fst (snd (contr (f x)) (x , refl))
    in has-inverse-equiv (g , G , linverse)

  -- definition 10.4.1
  Is-coh-invertible : {A B : Set} → (f : A → B) → Set
  Is-coh-invertible {A} {B} f =
    Σ (Has-inverse f) (λ { (g , G , H) → lwhisker G f ~ rwhisker f H })

  -- proposition 10.4.2
  coh-invertible-then-contr-fn : {A B : Set} → (f : A → B) → Is-coh-invertible f → Is-contr-fn f
  coh-invertible-then-contr-fn {A} {B} f ((g , G , H) , K) y =
    (center , C)
    where
      center : fib f y
      center = (g y , G y)
      C' : (x : fib f y) → Eq-fib f center x
      C' (x , refl) = (H x , K')
        where
          K' : G (f x) ≡ ap f (H x) · refl
          K' = begin
            G (f x)             ≡⟨ K x ⟩
            ap f (H x)          ≡⟨← (·-runit _) ⟩
            ap f (H x) · refl   ∎
      C : (x : fib f y) → center ≡ x
      C x = identity-from-Eq-fib f center x (C' x)

  -- definition 10.4.4
  comm-htpy : {A : Set} → (f : A → A) → (H : f ~ id) → (x : A) → (H (f x) ≡ ap f (H x))
  comm-htpy f H x = begin
    H (f x)                           ≡⟨← (·-runit (H (f x))) ⟩
    H (f x) · refl                    ≡⟨← ap (λ p → H (f x) · p) (·-rinv (H x)) ⟩
    H (f x) · (H x · (H x)⁻¹)         ≡⟨ ·-unassoc (H (f x)) (H x) ((H x)⁻¹) ⟩
    H (f x) · H x · (H x)⁻¹           ≡⟨← ap (λ p → H (f x) · p · (H x)⁻¹) (ap-id (H x)) ⟩
    H (f x) · ap id (H x) · (H x)⁻¹   ≡⟨← ap (λ p → p · (H x)⁻¹) (nat-htpy H (H x)) ⟩
    ap f (H x) · H x · (H x)⁻¹        ≡⟨ ·-assoc (ap f (H x)) (H x) ((H x)⁻¹) ⟩
    ap f (H x) · (H x · (H x)⁻¹)      ≡⟨ ap (λ p → ap f (H x) · p) (·-rinv (H x)) ⟩
    ap f (H x) · refl                 ≡⟨ ·-runit _ ⟩
    ap f (H x)                        ∎

  --   ┊   │     │   ┊
  --  [H]  │  =  │  [H]
  --   │   │     │   │
  --   f   f     f   f
  comm-htpy-whisk : {A : Set} → (f : A → A) → (H : f ~ id) → (lwhisker H f ~ rwhisker f H)
  comm-htpy-whisk = comm-htpy

  open Homotopy.Reasoning

  Is-coh-invertible-then-inverse-is-coh-invertible : {A B : Set} →
        (f : A → B) → (g : B → A) → (G : f ∘ g ~ id) → (H : g ∘ f ~ id) →
        (lwhisker G f ~ rwhisker f H) →
        (lwhisker H g ~ rwhisker g G) -- this makes ((f , H , G) , ∙) : Is-coh-invertible g
  Is-coh-invertible-then-inverse-is-coh-invertible {A} {B} f g G H K =
    begin-htpy
      --   ┊    │
      -- ╭[H]╮  │
      -- │   │  │
      -- g   f  g
      lwhisker H g

              ~⟨← hcomp-lunit (lwhisker H g) ⟩
      --  ┊    ┊    │
      --  ┊  ╭[H]╮  │
      --  ┊  │   │  │
      --     g   f  g
      hcomp (htpy-refl id) (lwhisker H g)

                ~⟨← hcomp-lhtpe (·ₕₜₚ-linv H) _ ⟩
      --    ┊       ┊    │
      --    ┊     ╭[H]╮  │
      -- ╭─[H]─╮  │   │  │
      -- g     f  │   │  │
      -- ╰[H⁻¹]╯  │   │  │
      --    ┊     │   │  │
      --          g   f  g
      (            hcomp (H ⁻¹ₕₜₚ ·ₕₜₚ H) (lwhisker H g)              )  ~⟨ hcomp-lconcat (H ⁻¹ₕₜₚ) H (lwhisker H g) ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (hcomp    H (lwhisker H g))  ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (hcomp-lr H (lwhisker H g))

                    ~⟨ ·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (hcomp-lr-rl H (lwhisker H g)) ⟩
      --    ┊       ┊    │
      -- ╭─[H]─╮    ┊    │
      -- │     │    ┊    │
      -- g     f  ╭[H]╮  │
      -- ╰[H⁻¹]╯  │   │  │
      --    ┊     │   │  │
      --          g   f  g
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (              hcomp-rl H (lwhisker H g)              )     ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ ((rwhisker (g ∘ f) (lwhisker H g)) ·ₕₜₚ (lwhisker H g))     ~⟨ ·ₕₜₚ-unassoc (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) _ _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ  (rwhisker (g ∘ f) (lwhisker H g)) ·ₕₜₚ (lwhisker H g)      ~⟨ ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (
                                                                                                            begin-htpy
                                                                                                              rwhisker (g ∘ f) (lwhisker H g)          ~⟨ rwhisker-comp g f _ ⟩
                                                                                                              rwhisker g (rwhisker f (lwhisker H g))   ~⟨⟩
                                                                                                              rwhisker g (lwhisker (rwhisker f H) g)   ∎-htpy
                                                                                                            )) _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker g (lwhisker (rwhisker f H) g)) ·ₕₜₚ (lwhisker H g)

                    ~⟨← ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (rwhisker-rhtpe _ (lwhisker-lhtpe K _))) _ ⟩
      --    ┊             │
      -- ╭─[H]─────────╮  │
      -- g     ╭[G]╮   │  │
      -- ╰[H⁻¹]╯   │   │  │
      --    ┊      │   │  │
      --           g   f  g
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker g (lwhisker (lwhisker G f) g)) ·ₕₜₚ (lwhisker H g) ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker g (lwhisker G (f ∘ g)))        ·ₕₜₚ (lwhisker H g)

                    ~⟨ ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (rwhisker-rhtpe _ (comm-htpy-whisk (f ∘ g) G))) _ ⟩
      --    ┊     │     ┊
      -- ╭─[H]─╮  │     ┊
      -- g     │  │   ╭[G]╮
      -- ╰[H⁻¹]╯  │   │   │
      --    ┊     │   │   │
      --          g   f   g
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ  (rwhisker g (rwhisker (f ∘ g) G)) ·ₕₜₚ (lwhisker H g)    ~⟨ ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (
                                                                                                          begin-htpy
                                                                                                            rwhisker g (rwhisker (f ∘ g) G)          ~⟨ rwhisker-rhtpe g (rwhisker-comp f g G) ⟩
                                                                                                            rwhisker g (rwhisker f (rwhisker g G))   ~⟨← rwhisker-comp g f _ ⟩
                                                                                                            rwhisker (g ∘ f) (rwhisker g G)          ∎-htpy
                                                                                                         )) _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ  (rwhisker (g ∘ f) (rwhisker g G)) ·ₕₜₚ (lwhisker H g)    ~⟨ ·ₕₜₚ-assoc (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) _ _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ ((rwhisker (g ∘ f) (rwhisker g G)) ·ₕₜₚ (lwhisker H g))   ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (              hcomp-rl H (rwhisker g G)              )

                    ~⟨← ·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (hcomp-lr-rl H (rwhisker g G)) ⟩
      --    ┊     │     ┊
      --    ┊     │   ╭[G]╮
      -- ╭─[H]─╮  │   │   │
      -- ╰[H⁻¹]╯  │   │   │
      --    ┊     │   │   │
      --          g   f   g
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (                hcomp-lr H (rwhisker g G)                 )   ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ ((lwhisker H (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker id (rwhisker g G)))   ~⟨ ·ₕₜₚ-unassoc (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) _ _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ  (lwhisker H (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker id (rwhisker g G))    ~⟨← ·ₕₜₚ-lhtpe (lwhisker-concat (H ⁻¹ₕₜₚ) H (g ∘ f ∘ g)) _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ ·ₕₜₚ H) (g ∘ f ∘ g))                         ·ₕₜₚ (rwhisker id (rwhisker g G))    ~⟨⟩
      hcomp (H ⁻¹ₕₜₚ ·ₕₜₚ H) (rwhisker g G)

              ~⟨ hcomp-lhtpe (·ₕₜₚ-linv H) _ ⟩
      -- ┊  │     ┊
      -- ┊  │   ╭[G]╮
      -- ┊  │   │   │
      --    g   f   g
      hcomp (htpy-refl id) (rwhisker g G)

              ~⟨ hcomp-lunit (rwhisker g G) ⟩
      -- │     ┊
      -- │   ╭[G]╮
      -- │   │   │
      -- g   f   g
      rwhisker g G   ∎-htpy

  -- lemma 10.4.5
  improve-section-of-inverse-to-be-coherent : {A B : Set} → (f : A → B) →
                                              ((g , G , H) : Has-inverse f) →
                                              (Σ (f ∘ g ~ id) (λ G' → lwhisker G' f ~ rwhisker f H))
  improve-section-of-inverse-to-be-coherent {A} {B} f (g , G , H) =
    let
      -- ╭───────────[G]╮
      -- │              │
      -- │      ╭─[H]╮  │
      -- ╰[G⁻¹]─╯    │  │
      --             │  │
      --             f  g
      G' : f ∘ g ~ id
      G' = lwhisker (G ⁻¹ₕₜₚ) (f ∘ g) ·ₕₜₚ (rwhisker f (lwhisker H g)) ·ₕₜₚ G

      K : lwhisker G' f ~ rwhisker f H
      K =
        begin-htpy
          --              ┊    │
          -- ╭───────────[G]╮  │
          -- │              │  │
          -- │      ╭─[H]╮  │  │
          -- ╰[G⁻¹]─╯    │  │  │
          --             │  │  │
          --             f  g  f
          lwhisker G' f                                                                                        ~⟨⟩
          lwhisker ((lwhisker (G ⁻¹ₕₜₚ) (f ∘ g)) ·ₕₜₚ (rwhisker f (lwhisker H g)) ·ₕₜₚ G) f                    ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ (lwhisker (rwhisker f (lwhisker H g)) f) ·ₕₜₚ (lwhisker G f)   ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker f (lwhisker H (g ∘ f))) ·ₕₜₚ (lwhisker G f)

                  ~⟨ ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) (rwhisker-rhtpe f
                      (comm-htpy-whisk (g ∘ f) H)
                    )) _ ⟩
          --     ┊     │     ┊
          --  ╭─[G]─╮  │     ┊
          --  │     │  │   ╭[H]╮
          --  ╰[G⁻¹]╯  │   │   │
          --     ┊     │   │   │
          --           f   g   f
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker f (rwhisker (g ∘ f) H)) ·ₕₜₚ (lwhisker G f)           ~⟨← ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) (rwhisker-comp f (g ∘ f) H)) _ ⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ  (rwhisker (f ∘ g ∘ f) H) ·ₕₜₚ (lwhisker G f)                   ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ  (rwhisker (f ∘ g ∘ f) H) ·ₕₜₚ (lwhisker (lwhisker G f) id)     ~⟨ ·ₕₜₚ-assoc (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) _ _ ⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ ((rwhisker (f ∘ g ∘ f) H) ·ₕₜₚ (lwhisker (lwhisker G f) id))    ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ (                hcomp-rl (lwhisker G f) H                 )

                  ~⟨← ·ₕₜₚ-rhtpe (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) (hcomp-lr-rl (lwhisker G f) H) ⟩
          --     ┊     │     ┊
          --     ┊     │   ╭[H]╮
          --  ╭─[G]─╮  │   │   │
          --  ╰[G⁻¹]╯  │   │   │
          --     ┊     │   │   │
          --           f   g   f
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ (hcomp-lr (lwhisker G f) H)                              ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ ((lwhisker (lwhisker G f) (g ∘ f)) ·ₕₜₚ (rwhisker f H))  ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ ((lwhisker G (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker f H))           ~⟨ ·ₕₜₚ-unassoc (lwhisker (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g)) f) _ _ ⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ  (lwhisker G (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker f H)            ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ  ·ₕₜₚ G) (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker f H)                                   ~⟨← ·ₕₜₚ-rhtpe (lwhisker (G ⁻¹ₕₜₚ  ·ₕₜₚ G) (f ∘ g ∘ f)) (rwhisker-id (rwhisker f H)) ⟩
          (lwhisker (G ⁻¹ₕₜₚ  ·ₕₜₚ G) (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker id (rwhisker f H))                     ~⟨⟩
          hcomp (G ⁻¹ₕₜₚ ·ₕₜₚ G) (rwhisker f H)

                  ~⟨ hcomp-lhtpe (·ₕₜₚ-linv G) _ ⟩
          --  ┊  │     ┊
          --  ┊  │   ╭[H]╮
          --  ┊  │   │   │
          --     f   g   f
          hcomp (htpy-refl id) (rwhisker f H)

                  ~⟨ hcomp-lunit _ ⟩
          -- │     ┊
          -- │   ╭[H]╮
          -- │   │   │
          -- f   g   f
          rwhisker f H ∎-htpy
    in (G' , K)

  Has-inverse-then-Is-coh-invertible : {A B : Set} → (f : A → B) → Has-inverse f → Is-coh-invertible f
  Has-inverse-then-Is-coh-invertible {A} {B} f (g , G , H) =
    let (G' , K) = improve-section-of-inverse-to-be-coherent f (g , G , H) in ((g , G' , H) , K)

  -- theorem 10.4.6
  Is-equiv-then-is-contr-fn : {A B : Set} → {f : A → B} → Is-equiv f → Is-contr-fn f
  Is-equiv-then-is-contr-fn {A} {B} {f} is-eqv =
    let
      has-inv     = equiv-has-inverse is-eqv
      is-coh-inv  = Has-inverse-then-Is-coh-invertible f has-inv
      is-contr-fn = coh-invertible-then-contr-fn f is-coh-inv
    in is-contr-fn

  Is-equiv-iff-is-contr-fn : {A B : Set} → {f : A → B} → (Is-equiv f ↔ Is-contr-fn f)
  Is-equiv-iff-is-contr-fn = (Is-equiv-then-is-contr-fn , contr-fn-then-equiv)

  -- corollary 10.4.7
  inverse-paths-type-is-contr : {A : Set} → (a : A) → Is-contr (Σ A (λ x → x ≡ a))
  inverse-paths-type-is-contr {A} a =
    let
      id-is-contr-fn : Is-contr-fn id
      id-is-contr-fn = Is-equiv-then-is-contr-fn Equivalence.id-is-equiv
    in id-is-contr-fn a -- `Σ A (λ x → x ≡ a)` is judgementally equal to `fib id a`

  -- exercise 10.1
  Is-contr-then-identity-is-contr : {A : Set} → Is-contr A → (x y : A) → Is-contr (x ≡ y)
  Is-contr-then-identity-is-contr {A} (a , C) x y =
    ((C x)⁻¹ · (C y), λ { refl → ·-linv (C x) })

  -- exercise 10.2
  retraction-preserves-contr : {A B : Set} → {f : A → B} → Retr f → Is-contr B → Is-contr A
  retraction-preserves-contr {A} {B} {f} (g , G) (bc , bC) =
    (g bc , λ a → begin
      g bc       ≡⟨ ap g (bC (f a)) ⟩
      g (f a)    ≡⟨ G a ⟩
      a          ∎
    )

  retract-of-contr-is-contr : {A B : Set} → Is-retract-of A B → Is-contr B → Is-contr A
  retract-of-contr-is-contr {A} {B} (f , retrf) contr = retraction-preserves-contr retrf contr

  -- exercise 10.3.a
  const-unit-is-equiv-then-contr : {A : Set} → Is-equiv (λ (a : A) → const unit a) → Is-contr A
  const-unit-is-equiv-then-contr {A} (_ , retr) = retraction-preserves-contr retr Unit-Is-contr

  map-to-unit-is-equiv-then-contr : {A : Set} → {f : A → Unit} → Is-equiv f → Is-contr A
  map-to-unit-is-equiv-then-contr {A} {f} eqv =
    const-unit-is-equiv-then-contr (
      is-equiv-preserved-by-homotopy (λ a →
        let (_ , C) = Unit-Is-contr
        in inverse (C (f a))
      ) eqv
    )

  contr-then-const-unit-is-equiv : {A : Set} → Is-contr A → Is-equiv (λ (a : A) → const unit a)
  contr-then-const-unit-is-equiv {A} (ac , C) =
    has-inverse-equiv ((λ _ → ac) , (λ { unit → refl }) , C)

  contr-iff-const-unit-is-equiv : {A : Set} → Is-contr A ↔ Is-equiv (λ (a : A) → const unit a)
  contr-iff-const-unit-is-equiv = (contr-then-const-unit-is-equiv , const-unit-is-equiv-then-contr)

  -- exercise 10.3.b
  cod-of-equiv-is-contr-then-dom-is-contr : {A B : Set} → {f : A → B} → Is-equiv f → Is-contr B → Is-contr A
  cod-of-equiv-is-contr-then-dom-is-contr {A} {B} {f} f-eqv b-contr =
    map-to-unit-is-equiv-then-contr (comp-equivs-is-equiv (contr-then-const-unit-is-equiv b-contr) f-eqv)

  -- exercise 10.3.b
  dom-of-equiv-is-contr-then-cod-is-contr : {A B : Set} → {f : A → B} → Is-equiv f → Is-contr A → Is-contr B
  dom-of-equiv-is-contr-then-cod-is-contr {A} {B} {f} f-eqv a-contr =
    map-to-unit-is-equiv-then-contr (comp-equivs-is-equiv (contr-then-const-unit-is-equiv a-contr) (≃-inverse-map-is-equiv f-eqv))

  dom-of-equiv-is-contr-iff-cod-is-contr : {A B : Set} → {f : A → B} → Is-equiv f → (Is-contr A ↔ Is-contr B)
  dom-of-equiv-is-contr-iff-cod-is-contr f-eqv = (dom-of-equiv-is-contr-then-cod-is-contr f-eqv , cod-of-equiv-is-contr-then-dom-is-contr f-eqv)

  open Equivalence.Symbolic
  equiv-then-contr-iff-contr : {A B : Set} → (A ≃ B) → (Is-contr A ↔ Is-contr B)
  equiv-then-contr-iff-contr (f , f-eqv) = dom-of-equiv-is-contr-iff-cod-is-contr f-eqv

  -- exercise 10.3.b
  any-map-between-contr-types-is-equiv : {A B : Set} → Is-contr A → Is-contr B → (f : A → B) → Is-equiv f
  any-map-between-contr-types-is-equiv {A} {B} a-contr b-contr f =
    latter-and-comp-are-equivs-then-former-is-equiv f (λ a → refl)
      (contr-then-const-unit-is-equiv b-contr)
      (contr-then-const-unit-is-equiv a-contr)

  open EmptyBasic
  any-map-into-empty-type-is-equiv : {A B : Set} → Is-empty B → (f : A → B) → Is-equiv f
  any-map-into-empty-type-is-equiv {A} {B} b-empty f =
    has-inverse-equiv (
      (λ b → absurd (b-empty b)),
      (λ b → absurd (b-empty b)),
      (λ a → absurd (b-empty (f a)))
    )

  dom-is-contr-then-is-equiv-iff-cod-is-contr : {A B : Set} → {f : A → B} → Is-contr A → Is-equiv f ↔ Is-contr B
  dom-is-contr-then-is-equiv-iff-cod-is-contr {A} {B} {f} a-contr =
    (
      (λ f-eqv → dom-of-equiv-is-contr-then-cod-is-contr f-eqv a-contr) ,
      (λ b-contr → any-map-between-contr-types-is-equiv a-contr b-contr f)
    )

  -- exercise 10.4
  module _ where
    open EmptyBasic

    inhabited-sum-is-not-contr : {A B : Set} → A → B → ¬ Is-contr (A +₀ B)
    inhabited-sum-is-not-contr _ b (left c , C) = Eq-Copr.left-neq-right (C (right b))
    inhabited-sum-is-not-contr a _ (right c , C) = Eq-Copr.left-neq-right ((C (left a)) ⁻¹)

    fin-is-not-contr-except-fin-one : {n : Nat} → (n ≢ succ zero) → ¬ (Is-contr (Fin n))
    fin-is-not-contr-except-fin-one {zero}           _    (() , _)
    fin-is-not-contr-except-fin-one {succ zero}     neq   _        = neq refl
    fin-is-not-contr-except-fin-one {succ (succ n)}  _  contr      = inhabited-sum-is-not-contr (right unit) unit contr

  -- exercise 10.5
  both-contr-then-product-is-contr : {A B : Set} → Is-contr A → Is-contr B → Is-contr (A × B)
  both-contr-then-product-is-contr {A} {B} (ca , CA) (cb , CB) =
    ((ca , cb) , λ { (x , y) → begin
      (ca , cb)           ≡⟨ ap2 (λ a b → (a , b)) (CA x) (CB y) ⟩
      (x , y)             ∎
    })
  product-is-contr-then-both-contr : {A B : Set} → Is-contr (A × B) → Is-contr A × Is-contr B
  product-is-contr-then-both-contr {A} {B} (cab , CAB) =
    let
      ca = fst cab
      cb = snd cab
    in (
      (ca , λ a → ap fst (CAB (a , cb))),
      (cb , λ b → ap snd (CAB (ca , b)))
    )

  -- exercise 10.6
  base-is-contr-then-pair-with-base-is-equiv : {A : Set} → ((a , C) : Is-contr A) →
                                               {B : A → Set} → Is-equiv {B a} {Σ A B} (λ (y : B a) → (a , y))
  base-is-contr-then-pair-with-base-is-equiv {A} contr@(a , _) {B} =
    has-inverse-equiv (g , sect , retr)
      where
        f : B a → Σ A B
        f y = (a , y)

        C : ContractionTo a
        C = untangle contr

        g : Σ A B → B a
        g (a' , y) = tr B ((C a')⁻¹) y

        sect : (f ∘ g) ~ id
        sect (a' , y) =
          begin
            (f ∘ g) (a' , y)                           ≡⟨⟩
            f (tr B ((C a')⁻¹) y)                      ≡⟨⟩
            (a , tr B ((C a')⁻¹) y)                    ≡⟨ ≡-Basic1.lift (C a') (tr B ((C a')⁻¹) y) ⟩
            (a' , tr B (C a') (tr B ((C a')⁻¹) y))     ≡⟨← ap (λ p → (a' , p)) (tr-concat ((C a')⁻¹) (C a') y) ⟩
            (a' , tr B ((C a')⁻¹ · C a') y)            ≡⟨ ap (λ p → (a' , tr B p y)) (·-linv (C a')) ⟩
            (a' , tr B refl y)                         ≡⟨⟩
            (a' , y)                                   ∎

        retr : (g ∘ f) ~ id
        retr y = begin
          g (f y)             ≡⟨⟩
          g (a , y)           ≡⟨⟩
          tr B ((C a)⁻¹) y    ≡⟨ ap (λ p → tr B (p ⁻¹) y) (untangled-contr-at-centre contr) ⟩
          tr B ((refl) ⁻¹) y  ≡⟨⟩
          y                   ∎

  Σ-≃-sections-at-base-center : {A : Set} → ((a , C) : Is-contr A) → {B : A → Set} → Σ A B ≃ B a
  Σ-≃-sections-at-base-center {A} contr {B} =
    ≃-comm (_ , base-is-contr-then-pair-with-base-is-equiv contr)

  -- exercise 10.7
  module _ where
    pr1-of : {A : Set} → (B : A → Set) → Σ A B → A
    pr1-of {A} B = Σ.fst

    -- exercise 10.7.a
    tr-from-fib-pr1-is-equiv : {A : Set} → {B : A → Set} → (a : A) → Is-equiv ((λ { ((x , y) , p) → tr B p y }) typed (fib (pr1-of B) a → B a))
    tr-from-fib-pr1-is-equiv {A} {B} a =
      has-inverse-equiv (
        (λ y → ((a , y) , refl)) ,
        (λ y → refl) ,
        (λ { ((x , y) , refl) → refl })
      )

    Is-contr-fam : {A : Set} → (B : A → Set) → Set
    Is-contr-fam {A} B = (a : A) → Is-contr (B a)

    -- exercise 10.7.b, (i) → (ii)
    pr1-equiv-then-contractible-family : {A : Set} → {B : A → Set} → Is-equiv (pr1-of B) → Is-contr-fam B
    pr1-equiv-then-contractible-family {A} {B} eqv a =
      let
        fib-pr1-is-contr : Is-contr (fib (pr1-of B) a)
        fib-pr1-is-contr = Is-equiv-then-is-contr-fn eqv a
      in dom-of-equiv-is-contr-then-cod-is-contr (tr-from-fib-pr1-is-equiv a) fib-pr1-is-contr

    -- exercise 10.7.b, (ii) → (i)
    contractible-family-then-pr1-is-equiv : {A : Set} → {B : A → Set} → Is-contr-fam B → Is-equiv (pr1-of B)
    contractible-family-then-pr1-is-equiv {A} {B} is-contr-b =
      let
        fib-pr1-is-contr : (a : A) → Is-contr (fib (pr1-of B) a)
        fib-pr1-is-contr a =
          let (y , C) = is-contr-b a
          in  (((a , y) , refl) , λ { ((.a , y') , refl) → ap (λ y'' → ((a , y'') , refl)) (C y') })
      in
        contr-fn-then-equiv fib-pr1-is-contr

    -- exercise 10.7.c, (i) → (ii)
    dep-pairing-Is-equiv-then-is-contr-fn-fam : {A : Set} → {B : A → Set} → (b : (x : A) → B x) →
                                              Is-equiv (λ (x : A) → (x , b x)) → Is-contr-fam B
    dep-pairing-Is-equiv-then-is-contr-fn-fam {A} {B} b dep-pairing-is-eqv =
      let
        dep-pairing : A → Σ A B
        dep-pairing = λ (x : A) → (x , b x)

        inv-pairing : Σ A B → A
        inv-pairing = ≃-inverse-map-for dep-pairing-is-eqv

        inv-pairing~pr1 : inv-pairing ~ pr1-of B
        inv-pairing~pr1 =
          λ { (x , y) →
            let pairing-inv-pairing-xy≡xy = ≃-inverse-map-is-sect-of-original dep-pairing-is-eqv (x , y)
                inv-pairing-xy≡x = ap Σ.fst pairing-inv-pairing-xy≡xy
            in
              begin
                inv-pairing (x , y) ≡⟨ inv-pairing-xy≡x ⟩
                x                   ≡⟨⟩
                pr1-of B (x , y)    ∎
          }
      in
        pr1-equiv-then-contractible-family (
          is-equiv-preserved-by-homotopy inv-pairing~pr1
            (≃-inverse-map-is-equiv dep-pairing-is-eqv)
        )

    -- exercise 10.7.c, (ii) → (i)
    is-contr-fam-then-dep-pairing-is-equiv : {A : Set} → {B : A → Set} → (b : (x : A) → B x) →
                                              Is-contr-fam B → Is-equiv (λ (x : A) → (x , b x))
    is-contr-fam-then-dep-pairing-is-equiv {A} {B} b is-contr-b =
      has-inverse-equiv (
        pr1-of B ,
        (λ { (x , y) →
          begin
            ((λ (x : A) → (x , b x)) ∘ (pr1-of B)) (x , y) ≡⟨⟩
            (x , b x)                                      ≡⟨ ap (λ y' → (x , y')) (two-points-eq-in-contr-type (is-contr-b x) (b x) y) ⟩
            (x , y)                                        ≡⟨⟩
            id (x , y)                                     ∎
        }) ,
        (λ a → refl)
      )

  -- exercise 10.8
  module _ where
    open Equivalence.Symbolic

    decomposeToFibs : {A B : Set} → (f : A → B) → (a : A) → Σ B (λ y → fib f y)
    decomposeToFibs {A} {B} f a = ((f a) , (a , refl))

    glueFibers : {A B : Set} → (f : A → B) → Σ B (λ y → fib f y) → A
    glueFibers {A} {B} f (b , (a , p)) = a

    decompose-glue-is-id : {A B : Set} → (f : A → B) → Is-sect-of (decomposeToFibs f) (glueFibers f)
    decompose-glue-is-id {A} {B} f (b , (a , refl)) = refl

    glue-decompose-is-id : {A B : Set} → (f : A → B) → Is-retraction-of (decomposeToFibs f) (glueFibers f)
    glue-decompose-is-id {A} {B} f a = refl

    decomposeToFibs-is-equiv : {A B : Set} → (f : A → B) → Is-equiv (decomposeToFibs f)
    decomposeToFibs-is-equiv {A} {B} f =
      has-inverse-equiv (glueFibers f , decompose-glue-is-id f , glue-decompose-is-id f)

    glueFibers-is-equiv : {A B : Set} → (f : A → B) → Is-equiv (glueFibers f)
    glueFibers-is-equiv {A} {B} f = ≃-inverse-map-is-equiv (decomposeToFibs-is-equiv f)

    fiber-decomposition : {A B : Set} → (f : A → B) → A ≃ (Σ B (λ y → fib f y))
    fiber-decomposition {A} {B} f = (decomposeToFibs f , decomposeToFibs-is-equiv f)

    fibrantReplacement : {A B : Set} → (f : A → B) → (Σ B (λ y → fib f y)) → B
    fibrantReplacement f = Σ.fst

    fibrantReplacement-factors : {A B : Set} → (f : A → B) → f ~ ((fibrantReplacement f) ∘ (decomposeToFibs f))
    fibrantReplacement-factors {A} {B} f a = refl
