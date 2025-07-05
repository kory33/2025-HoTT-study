module _ where
  open import section-09 public

  open Homotopy
  open Homotopy.Symbolic
  open ≡-Basic
  open ≡-Reasoning

  -- 10.1.1
  Is-contr : Set → Set
  Is-contr A = Σ A (λ c → (x : A) → c ≡ x)

  -- 10.1.2
  contraction-to : {A : Set} → (c : A) → Set
  contraction-to c = const c ~ id

  -- 10.1.3
  Unit-Is-contr : Is-contr Unit
  Unit-Is-contr = (unit , Unit-ind { λ (u : Unit) → unit ≡ u } refl)

  -- 10.1.4
  identity-with-an-endpoint-fixed-Is-contr : {A : Set} → (a : A) → Is-contr (Σ A (λ x → a ≡ x))
  identity-with-an-endpoint-fixed-Is-contr a =
    ((a , refl) , λ pt → ≡-Basic1.refl-uniq a pt)

  -- 10.2.1
  ev-pt : {A : Set} → {B : (x : A) → Set} → (a : A) → (f : (x : A) → B x) → B a
  ev-pt a f = f a

  -- 10.2.3
  contr-then-sing-ind : {A : Set} → Is-contr A → {B : A → Set} →
    Σ A (λ a → Σ (B a → (x : A) → B x) (λ ind-sing-a → ev-pt a ∘ ind-sing-a ~ id))
  contr-then-sing-ind {A} (a , C) {B} =
    let
      C' : (x : A) → a ≡ x
      C' x = (C a)⁻¹ · (C x)
      p : C' a ≡ refl
      p = ·-linv (C a)

      ind-sing-a : B a → (x : A) → B x
      ind-sing-a b x = tr B (C' x) b
      comp-sing-a : ev-pt a ∘ ind-sing-a ~ id
      comp-sing-a = λ b → begin
        (ev-pt a ∘ ind-sing-a) b ≡⟨⟩
        tr B (C' a) b            ≡⟨ ap (λ t → tr B t b) p ⟩
        tr B refl b              ≡⟨⟩
        b                        ≡⟨⟩
        id b                     ∎
    in
      (a , ind-sing-a , comp-sing-a)

  -- 10.2.3
  -- To properly phrase "singleton induction" we need to use Set₁ and the corresponding
  -- (or universe-polymorphic) Σ types, but for our purposes it suffices to consider
  -- just one type family B(x) := a ≡ x, since that is the only induction we will use.
  sing-ind-on-identity-then-contr : {A : Set} →
    Σ A (λ a → Σ (a ≡ a → (x : A) → a ≡ x) (λ ind-sing-a → ev-pt a ∘ ind-sing-a ~ id)) →
    Is-contr A
  sing-ind-on-identity-then-contr (a , ind-sing-a , _) =
    (a , λ x → ind-sing-a refl x)

  -- 10.3.1
  fib : {A B : Set} → (f : A → B) → (b : B) → Set
  fib {A} {B} f b = Σ A (λ a → f a ≡ b)

  -- 10.3.2
  Eq-fib : {A B : Set} → (f : A → B) → {y : B} → fib f y → fib f y → Set
  Eq-fib f (x , p) (x' , p') = Σ (x ≡ x') (λ α → p ≡ (ap f α) · p')

  Eq-fib-refl : {A B : Set} → (f : A → B) → {y : B} → (x : fib f y) → Eq-fib f x x
  Eq-fib-refl f (x , p) = (refl , refl)

  Eq-fib-from-identity : {A B : Set} → (f : A → B) → {y : B} →
                         {x x' : fib f y} → (p : x ≡ x') → Eq-fib f x x'
  Eq-fib-from-identity f refl = Eq-fib-refl f _

  open Equivalence

  identity-from-Eq-fib : {A B : Set} → (f : A → B) → {y : B} → {x x' : fib f y} →
    Eq-fib f x x' → x ≡ x'
  identity-from-Eq-fib f (refl , refl) = refl

  -- 10.3.3
  Eq-fib-from-identity-is-equiv : {A B : Set} → (f : A → B) → {y : B} → {x x' : fib f y} →
                                  Is-equiv (Eq-fib-from-identity f {y} {x} {x'})
  Eq-fib-from-identity-is-equiv f {y} {x} {x'} =
    has-inverse-equiv (identity-from-Eq-fib f , rinverse , linverse)
    where
      rinverse : (Eq-fib-from-identity f) ∘ (identity-from-Eq-fib f) ~ id
      rinverse (refl , refl) = refl
      linverse : (identity-from-Eq-fib f) ∘ (Eq-fib-from-identity f) ~ id
      linverse refl = refl

  -- 10.3.4
  Is-contr-fn : {A B : Set} → (f : A → B) → Set
  Is-contr-fn {A} {B} f = (b : B) → Is-contr (fib f b)

  open Σ

  -- 10.3.5
  contr-fn-then-equiv : {A B : Set} → (f : A → B) → Is-contr-fn f → Is-equiv f
  contr-fn-then-equiv {A} {B} f contr =
    let
      gG : (y : B) → fib f y
      gG y = contr y .fst
      g : B → A
      g y = gG y .fst
      G : (y : B) → f (g y) ≡ y
      G y = gG y .snd

      linverse : g ∘ f ~ id
      linverse x =
        let
          (_ , C) = contr (f x)
          q = begin
            -- the LHS is THE center of contraction of fib f (f x)
            (g (f x) , G (f x))   ≡⟨ C (x , refl) ⟩
            (x , refl)            ∎
        in ap fst q
    in has-inverse-equiv (g , G , linverse)

  -- 10.4.1
  Is-coh-invertible : {A B : Set} → (f : A → B) → Set
  Is-coh-invertible {A} {B} f =
    Σ (Has-inverse f) (λ { (g , G , H) → lwhisker G f ~ rwhisker f H })

  -- 10.4.2
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
            ap f (H x)          ≡⟨ inverse (·-runit _) ⟩
            ap f (H x) · refl   ∎
      C : (x : fib f y) → center ≡ x
      C x = identity-from-Eq-fib f (C' x)

  -- 10.4.4
  comm-htpy : {A : Set} → (f : A → A) → (H : f ~ id) → (x : A) → (H (f x) ≡ ap f (H x))
  comm-htpy f H x = begin
    H (f x)                           ≡⟨ inverse (·-runit (H (f x))) ⟩
    H (f x) · refl                    ≡⟨ ap (λ p → H (f x) · p) (inverse (·-rinv (H x))) ⟩
    H (f x) · (H x · (H x)⁻¹)         ≡⟨ unassoc (H (f x)) (H x) ((H x)⁻¹) ⟩
    H (f x) · H x · (H x)⁻¹           ≡⟨ ap (λ p → H (f x) · p · (H x)⁻¹) (inverse (ap-id (H x))) ⟩
    H (f x) · ap id (H x) · (H x)⁻¹   ≡⟨ ap (λ p → p · (H x)⁻¹) (inverse (nat-htpy H (H x))) ⟩
    ap f (H x) · H x · (H x)⁻¹        ≡⟨ assoc (ap f (H x)) (H x) ((H x)⁻¹) ⟩
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
      --      ┊         ┊    │
      --      ┊       ╭[H]╮  │
      -- ╭───[H]───╮  │   │  │
      -- g         f  │   │  │
      -- ╰[H ⁻¹ₕₜₚ]╯  │   │  │
      --      ┊       │   │  │
      --              g   f  g
      (            hcomp (H ⁻¹ₕₜₚ ·ₕₜₚ H) (lwhisker H g)              )  ~⟨ hcomp-lconcat (H ⁻¹ₕₜₚ) H (lwhisker H g) ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (hcomp    H (lwhisker H g))  ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (hcomp-lr H (lwhisker H g))

                    ~⟨ ·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (hcomp-lr-rl H (lwhisker H g)) ⟩
      --      ┊         ┊    │
      -- ╭───[H]───╮    ┊    │
      -- │         │    ┊    │
      -- g         f  ╭[H]╮  │
      -- ╰[H ⁻¹ₕₜₚ]╯  │   │  │
      --      ┊       │   │  │
      --              g   f  g
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
      --      ┊               │
      -- ╭───[H]───────────╮  │
      -- g         ╭[G]╮   │  │
      -- ╰[H ⁻¹ₕₜₚ]╯   │   │  │
      --      ┊        │   │  │
      --               g   f  g
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker g (lwhisker (lwhisker G f) g)) ·ₕₜₚ (lwhisker H g) ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker g (lwhisker G (f ∘ g)))        ·ₕₜₚ (lwhisker H g)

                    ~⟨ ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (rwhisker-rhtpe _ (comm-htpy-whisk (f ∘ g) G))) _ ⟩
      --      ┊       │     ┊  
      -- ╭───[H]───╮  │     ┊  
      -- g         │  │   ╭[G]╮
      -- ╰[H ⁻¹ₕₜₚ]╯  │   │   │
      --      ┊       │   │   │
      --              g   f   g
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
      --      ┊       │     ┊  
      --      ┊       │   ╭[G]╮
      -- ╭───[H]───╮  │   │   │
      -- ╰[H ⁻¹ₕₜₚ]╯  │   │   │
      --      ┊       │   │   │
      --              g   f   g
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
