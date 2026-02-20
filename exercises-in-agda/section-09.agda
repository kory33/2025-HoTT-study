open import Function.Base using (case_of_)

module _ where
  open import section-08 public

  -- definition 9.1.2
  Homotopy : {A : Set} → {B : (x : A) → Set} → (f g : (x : A) → B x) → Set
  Homotopy {A} f g = (x : A) → f x ≡ g x

  module Homotopy where
    open ≡-Basic

    module Symbolic where
      -- When K : f ~ g, we will diagramatically write the situation as:
      --         g 
      --         │ 
      --        [K]
      --         │ 
      --         f 
      _~_ : {A : Set} → {B : (x : A) → Set} → (f g : (x : A) → B x) → Set
      f ~ g = Homotopy f g

      infixl 5 _~_
    open Symbolic

    -- example 9.1.3
    module _ where
      open BoolBasic
      neg-neg-bool : negBool ∘ negBool ~ id
      neg-neg-bool true = refl
      neg-neg-bool false = refl

    -- definition 9.1.5 + proposition 9.1.6
    module _ where
      private variable
        A : Set
        B : (x : A) → Set

      --       f       
      --       │       
      --  [htpy-refl f]
      --       │       
      --       f       
      htpy-refl    : (f : (x : A) → B x)     → f ~ f
      htpy-refl f x = refl

      --  g                  f          
      --  │                  │          
      -- [K]  then  [htpy-inverse f g K]
      --  │                  │          
      --  f                  g          
      htpy-inverse : (f g : (x : A) → B x)   → f ~ g → g ~ f
      htpy-inverse f g K x = inverse (K x)

      --  h                      h            
      --  │                      │            
      -- [G]                     │            
      --  │                      │            
      --  │ g   then  [htpy-concat f g h H G] 
      --  │                      │            
      -- [H]                     │            
      --  │                      │            
      --  f                      f            
      htpy-concat  : (f g h : (x : A) → B x) → f ~ g → g ~ h → f ~ h
      htpy-concat f g h H G x = (H x) · (G x)

      htpy-eq-refl : (f : (x : A) → B x) → {g : (x : A) → B x} → (f ≡ g) → f ~ g
      htpy-eq-refl f {g} refl = htpy-refl f

      module HomotopyGroupoidSymbolic where
        --  h               h      
        --  │               │      
        -- [G]              │      
        --  │               │      
        --  │ g   then  [H ·ₕₜₚ G] 
        --  │               │      
        -- [H]              │      
        --  │               │      
        --  f               f      
        _·ₕₜₚ_ : {f g h : (x : A) → B x} → f ~ g → g ~ h → f ~ h
        H ·ₕₜₚ G = htpy-concat _ _ _ H G

        infixl 40 _·ₕₜₚ_

        --  g             f     
        --  │             │     
        -- [K]  then  [K ⁻¹ₕₜₚ] 
        --  │             │     
        --  f             g     
        --
        -- In diagrams we will usually write K⁻¹ for K ⁻¹ₕₜₚ.
        _⁻¹ₕₜₚ : {f g : (x : A) → B x} → f ~ g → g ~ f
        H ⁻¹ₕₜₚ = htpy-inverse _ _ H
        infix 54 _⁻¹ₕₜₚ

      open ≡-Reasoning
      open HomotopyGroupoidSymbolic

      module Reasoning where
        open Symbolic public
        open HomotopyGroupoidSymbolic public

        infix  1 begin-htpy_
        infixr 2 step-~-∣ step-~-⟩ step-~-⟩⁻¹
        infix  3 _∎-htpy

        begin-htpy_ : {A : Set} → {B : (x : A) → Set} → {f g : (x : A) → B x} → f ~ g → f ~ g
        begin-htpy f~g = f~g

        step-~-∣ : {A : Set} → {B : (x : A) → Set} → (f : (x : A) → B x) → {g : (x : A) → B x} → f ~ g → f ~ g
        step-~-∣ f f~g = f~g

        step-~-⟩ : {A : Set} → {B : (x : A) → Set} → (f : (x : A) → B x) → {g h : (x : A) → B x} → f ~ g → g ~ h → f ~ h
        step-~-⟩ f f~g g~h = f~g ·ₕₜₚ g~h

        step-~-⟩⁻¹ : {A : Set} → {B : (x : A) → Set} → (f : (x : A) → B x) → {g h : (x : A) → B x} → g ~ f → g ~ h → f ~ h
        step-~-⟩⁻¹ f g~f g~h = (g~f ⁻¹ₕₜₚ) ·ₕₜₚ g~h

        syntax step-~-∣   f f~g      =  f ~⟨⟩ f~g
        syntax step-~-⟩   f f~g g~h  =  f ~⟨ f~g ⟩ g~h
        syntax step-~-⟩⁻¹ f g~f g~h  =  f ~⟨← g~f ⟩ g~h

        _∎-htpy : {A : Set} → {B : (x : A) → Set} → (f : (x : A) → B x) → f ~ f
        x ∎-htpy  =  htpy-refl x

      open Reasoning

      private variable
        f g h i : (x : A) → B x

      -- "Left-homotope" a concatenation.
      --
      -- If p : H1 ~ H2, then:
      --     │       │  
      --    [K]     [K] 
      --     │   ~   │  
      --   [H1]    [H2] 
      --     │       │  
      --     f       f  
      ·ₕₜₚ-lhtpe : {A B : Set} → {f g h : A → B} → {H1 H2 : f ~ g} → (p : H1 ~ H2) → (K : g ~ h) → (H1 ·ₕₜₚ K ~ H2 ·ₕₜₚ K)
      ·ₕₜₚ-lhtpe {A} {B} {f} {g} {h} {H1} {H2} p K x =
        begin
          (H1 ·ₕₜₚ K) x         ≡⟨⟩
          (H1 x) · (K x)        ≡⟨ ap (λ y → y · K x) (p x) ⟩
          (H2 x) · (K x)        ≡⟨⟩
          (H2 ·ₕₜₚ K) x         ∎

      -- "Right-homotope" a concatenation.
      --
      -- If p : K1 ~ K2, then:
      --     │       │  
      --   [K1]    [K2] 
      --     │   ~   │  
      --    [H]     [H] 
      --     │       │  
      --     f       f  
      ·ₕₜₚ-rhtpe : {A B : Set} → {f g h : A → B} → (H : f ~ g) → {K1 K2 : g ~ h} → (p : K1 ~ K2) → (H ·ₕₜₚ K1 ~ H ·ₕₜₚ K2)
      ·ₕₜₚ-rhtpe {A} {B} {f} {g} {h} H {K1} {K2} p x =
        begin
          (H ·ₕₜₚ K1) x         ≡⟨⟩
          (H x) · (K1 x)        ≡⟨ ap (λ y → H x · y) (p x) ⟩
          (H x) · (K2 x)        ≡⟨⟩
          (H ·ₕₜₚ K2) x         ∎

      --     │       │          │       │ 
      --    [L]      │      [K ·ₕₜₚ L]  │ 
      --     │       │   =      │       │ 
      -- [H ·ₕₜₚ K]  │         [H]      │ 
      --     │       │          │       │ 
      --     f       x          f       x 
      -- By an abuse of notation, x in the diagram stands for const x : Unit → A.
      -- When we don't have function extensionality, this is the best we can say about
      -- these "equality" between homotopies.
      --
      -- The same claim can be written using a higher homotopy, and we will usually be writing in this way:
      --     │              │     
      --    [L]         [K ·ₕₜₚ L]
      --     │       ~      │     
      -- [H ·ₕₜₚ K]        [H]    
      --     │              │     
      --     f              f     
      ·ₕₜₚ-assoc : (H : f ~ g) → (K : g ~ h) → (L : h ~ i) → H ·ₕₜₚ K ·ₕₜₚ L ~ H ·ₕₜₚ (K ·ₕₜₚ L)
      ·ₕₜₚ-assoc H K L x = ·-assoc (H x) (K x) (L x)

      ·ₕₜₚ-unassoc : (H : f ~ g) → (K : g ~ h) → (L : h ~ i) → H ·ₕₜₚ (K ·ₕₜₚ L) ~ H ·ₕₜₚ K ·ₕₜₚ L
      ·ₕₜₚ-unassoc H K L = (·ₕₜₚ-assoc H K L) ⁻¹ₕₜₚ

      --       │            │  
      --      [H]          [H] 
      --       │        ~   │  
      -- [htpy-refl f]      │  
      --       │            │  
      --       f            f  
      ·ₕₜₚ-lunit : (H : f ~ g) → (htpy-refl f) ·ₕₜₚ H ~ H
      ·ₕₜₚ-lunit H x = ·-lunit (H x)

      --       g             g  
      --       │             │  
      -- [htpy-refl g]       │  
      --       │        ~    │  
      --      [H]           [H] 
      --       │             │  
      --       f             f  
      ·ₕₜₚ-runit : (H : f ~ g) → H ·ₕₜₚ (htpy-refl g) ~ H
      ·ₕₜₚ-runit H x = ·-runit (H x)

      --       g       g 
      --       │       │ 
      --      [H]      │ 
      --       │    ~  │ 
      --     [H⁻¹]     │ 
      --       │       │ 
      --       f       f 
      ·ₕₜₚ-linv : (H : f ~ g) → (H ⁻¹ₕₜₚ ·ₕₜₚ H) ~ htpy-refl g
      ·ₕₜₚ-linv H x = ·-linv (H x)

      --       g       g 
      --       │       │ 
      --     [H⁻¹]     │ 
      --       │    ~  │ 
      --      [H]      │ 
      --       │       │ 
      --       f       f 
      ·ₕₜₚ-rinv : (H : f ~ g) → (H ·ₕₜₚ H ⁻¹ₕₜₚ) ~ htpy-refl f
      ·ₕₜₚ-rinv H x = ·-rinv (H x)

      -- definition 10.4.3
      nat-htpy : {A B : Set} → {f g : A → B} → (H : f ~ g) → {x y : A} → (p : x ≡ y) → (ap f p · H y ≡ H x · ap g p)
      nat-htpy {A} {B} {f} {g} H {x} {y} refl =
        begin
          ap f refl · H x        ≡⟨⟩
          refl · H x             ≡⟨⟩
          H x                    ≡⟨← (·-runit (H x)) ⟩
          H x · refl             ≡⟨⟩
          H x · ap g refl        ∎

    -- definition 9.1.7
    module _ where
      open HomotopyGroupoidSymbolic
      open ≡-Reasoning
      open Reasoning

      private variable
        A B C : Set

      --  h    g 
      --  │    │ 
      --  │   [G]
      --  │    │ 
      --  h    f 
      rwhisker : (h : B → C) → {f g : A → B} → (G : f ~ g) → h ∘ f ~ h ∘ g
      rwhisker h G x = ap h (G x)

      --  ┊   │       │  
      --  ┊  [G]  ~  [G] 
      --  ┊   │       │  
      --  ┊   │       │  
      --      f       f  
      rwhisker-id : {f g : A → B} → (G : f ~ g) → rwhisker id G ~ G
      rwhisker-id G x =
        begin
          rwhisker id G x         ≡⟨⟩
          ap id (G x)             ≡⟨ ap-id (G x) ⟩
          G x                     ∎

      --    │   │      │   │   │  
      --    │  [G]  ~  │   │  [G] 
      --    │   │      │   │   │  
      --    │   │      │   │   │  
      --   f∘g  h      f   g   h  
      rwhisker-comp : {A B C D : Set} → (f : C → D) → (g : B → C) → {h k : A → B} → (G : h ~ k) →
                      rwhisker (f ∘ g) G ~ rwhisker f (rwhisker g G)
      rwhisker-comp {A} {B} {C} {D} f g {h} {k} G x =
        begin
          rwhisker (f ∘ g) G x           ≡⟨⟩
          ap (f ∘ g) (G x)               ≡⟨ ap-comp f g (G x) ⟩
          ap f (ap g (G x))              ≡⟨⟩
          rwhisker f (rwhisker g G) x    ∎

      -- If p : G1 ~ G2, then:
      --  h   g       h   g   
      --  │   │       │   │   
      --  │  [G1]  ~  │  [G2] 
      --  │   │       │   │   
      --  h   f       h   f   
      rwhisker-rhtpe : {A B C : Set} → (h : B → C) → {f g : A → B} → {G1 G2 : f ~ g} → (p : G1 ~ G2) → rwhisker h G1 ~ rwhisker h G2
      rwhisker-rhtpe {A} {B} {C} h {f} {g} {G1} {G2} p x =
        begin
          rwhisker h G1 x         ≡⟨⟩
          ap h (G1 x)             ≡⟨ ap (λ t → ap h t) (p x) ⟩
          ap h (G2 x)             ≡⟨⟩
          rwhisker h G2 x         ∎

      --  h    f 
      --  │    │ 
      -- [H]   │ 
      --  │    │ 
      --  g    f 
      lwhisker : {g h : B → C} → (H : g ~ h) → (f : A → B) → g ∘ f ~ h ∘ f
      lwhisker H f x = H (f x)
    
      --  │   ┊      │  
      -- [G]  ┊  ~  [G] 
      --  │   ┊      │  
      --  │   ┊      │  
      --  f          f  
      lwhisker-id : {f g : A → B} → (G : f ~ g) → lwhisker G id ~ G
      lwhisker-id G x =
        begin
          lwhisker G id x         ≡⟨⟩
          id (G x)                ≡⟨⟩
          G x                     ∎

      --   │   │       │   │   │  
      --  [G]  │   ~  [G]  │   │  
      --   │   │       │   │   │  
      --   │   │       │   │   │  
      --   h  f∘g      h   f   g  
      lwhisker-comp : {A B C D : Set} → {h k : C → D} → (G : h ~ k) → (f : B → C) → (g : A → B) → 
                      lwhisker G (f ∘ g) ~ lwhisker (lwhisker G f) g
      lwhisker-comp {A} {B} {C} {D} {h} {k} G f g x = refl

      --   │   │         │      │ 
      --  [H]  │         │      │ 
      --   │   │  =  [G ·ₕₜₚ H] │ 
      --  [G]  │         │      │ 
      --   │   │         │      │ 
      --   f   k         f      k 
      lwhisker-concat : {A B C : Set} → {f g h : B → C} → (G : f ~ g) → (H : g ~ h) → (k : A → B) →
                      lwhisker (G ·ₕₜₚ H) k ~ (lwhisker G k) ·ₕₜₚ (lwhisker H k)
      lwhisker-concat {A} {B} {C} {f} {g} {h} G H k x = refl

      -- If p : G1 ~ G2, then:
      --  g    h      g    h 
      --  │    │      │    │ 
      -- [G1]  │  ~  [G2]  │ 
      --  │    │      │    │ 
      --  f    h      f    h 
      lwhisker-lhtpe : {A B C : Set} → {f g : B → C} → {G1 G2 : f ~ g} → (p : G1 ~ G2) → (h : A → B) → lwhisker G1 h ~ lwhisker G2 h
      lwhisker-lhtpe {A} {B} {C} {f} {g} {G1} {G2} p h x =
        begin
          lwhisker G1 h x         ≡⟨⟩
          G1 (h x)                ≡⟨ p (h x) ⟩
          G2 (h x)                ≡⟨⟩
          lwhisker G2 h x         ∎

      -- horizontal composition

      --  k    g  
      --  │    │  
      --  │   [G] 
      -- [K]   │  
      --  │    │  
      --  h    f  
      hcomp-lr : {A B C : Set} → {h k : B → C} → (K : h ~ k) → {f g : A → B} → (G : f ~ g) → (h ∘ f) ~ (k ∘ g)
      hcomp-lr {A} {B} {C} {h} {k} K {f} {g} G = (lwhisker K f) ·ₕₜₚ (rwhisker k G)

      --  k    g  
      --  │    │  
      -- [K]   │  
      --  │   [G] 
      --  │    │  
      --  h    f  
      hcomp-rl : {A B C : Set} → {h k : B → C} → (K : h ~ k) → {f g : A → B} → (G : f ~ g) → (h ∘ f) ~ (k ∘ g)
      hcomp-rl {A} {B} {C} {h} {k} K {f} {g} G = (rwhisker h G) ·ₕₜₚ (lwhisker K g)

      --  k    g  
      --  │    │  
      --  │   [G] 
      -- [K]   │  
      --  │    │  
      --  h    f  
      hcomp : {h k : B → C} → (h ~ k) → {f g : A → B} → (f ~ g) → (h ∘ f) ~ (k ∘ g)
      hcomp = hcomp-lr

      --  k    g       k    g  
      --  │    │       │    │  
      --  │   [G]  ~  [K]   │  
      -- [K]   │       │   [G] 
      --  │    │       │    │  
      --  h    f       h    f  
      hcomp-lr-rl : {A B C : Set} →
                              {h k : B → C} → (K : h ~ k) → {f g : A → B} → (G : f ~ g) → 
                              hcomp-lr K G ~ hcomp-rl K G
      hcomp-lr-rl {A} {B} {C} {h} {k} K {f} {g} G x =
        begin
          hcomp-lr K G x                 ≡⟨⟩
          ((lwhisker K f) ·ₕₜₚ (rwhisker k G)) x   ≡⟨⟩
          (lwhisker K f x) · (rwhisker k G x)      ≡⟨⟩
          K (f x) · ap k (G x)                     ≡⟨← (nat-htpy K (G x)) ⟩
          ap h (G x) · K (g x)                     ≡⟨⟩
          ((rwhisker h G) ·ₕₜₚ (lwhisker K g)) x   ≡⟨⟩
          hcomp-rl K G x                 ∎

      --  h    f       h        f        
      --  │    │       │        │        
      --  │    │   ~   │  [htpy-refl f]  
      -- [H]   │      [H]       │        
      --  │    │       │        │        
      --  g    f       g        f        
      lwhisker-to-hcomp : {A B C : Set} → {g h : B → C} → (H : g ~ h) → (f : A → B) →
                                    lwhisker H f ~ hcomp H (htpy-refl f)
      lwhisker-to-hcomp {A} {B} {C} {g} {h} H f =
        begin-htpy
          lwhisker H f                                         ~⟨ (·ₕₜₚ-runit (lwhisker H f)) ⁻¹ₕₜₚ ⟩
          lwhisker H f ·ₕₜₚ htpy-refl (h ∘ f)                  ~⟨⟩
          lwhisker H f ·ₕₜₚ rwhisker h (htpy-refl f)           ~⟨⟩
          hcomp H (htpy-refl f)                      ∎-htpy

      --  h    g           h        g  
      --  │    │           │        │  
      --  │   [G]  ~       │       [G] 
      --  │    │     [htpy-refl h]  │  
      --  │    │           │        │  
      --  h    f           h        f  
      rwhisker-to-hcomp : {A B C : Set} → (h : B → C) → {f g : A → B} → (G : f ~ g) →
                                    rwhisker h G ~ hcomp (htpy-refl h) G
      rwhisker-to-hcomp {A} {B} {C} h {f} {g} G =
        begin-htpy
          rwhisker h G                                       ~⟨ (·ₕₜₚ-lunit (rwhisker h G)) ⁻¹ₕₜₚ ⟩
          (htpy-refl (h ∘ f)) ·ₕₜₚ (rwhisker h G)            ~⟨⟩
          (lwhisker (htpy-refl h) f) ·ₕₜₚ (rwhisker h G)     ~⟨⟩
          hcomp (htpy-refl h) G                    ∎-htpy

      --       ┊         │       │  
      --       ┊        [G]  ~  [G] 
      -- [htpy-refl id]  │       │  
      --       ┊         │       │  
      --                 f       f  
      hcomp-lunit : {A B : Set} → {f g : A → B} → (G : f ~ g) →
                              hcomp (htpy-refl id) G ~ G
      hcomp-lunit {A} {B} {f} {g} G =
        begin-htpy
          hcomp (htpy-refl id) G                     ~⟨⟩
          (lwhisker (htpy-refl id) f) ·ₕₜₚ (rwhisker id G)     ~⟨⟩
          htpy-refl (id ∘ f) ·ₕₜₚ (rwhisker id G)              ~⟨ ·ₕₜₚ-lunit (rwhisker id G) ⟩
          rwhisker id G                                        ~⟨ rwhisker-id G ⟩
          G                                                    ∎-htpy

      --  │        ┊             │  
      --  │  [htpy-refl id]      │  
      -- [G]       ┊         ~  [G] 
      --  │        ┊             │  
      --  f                      f  
      hcomp-runit : {A B : Set} → {f g : A → B} → (G : f ~ g) →
                              hcomp G (htpy-refl id) ~ G
      hcomp-runit {A} {B} {f} {g} G =
        begin-htpy
          hcomp G (htpy-refl id)                     ~⟨⟩
          (lwhisker G id) ·ₕₜₚ (rwhisker g (htpy-refl id))     ~⟨⟩
          (lwhisker G id) ·ₕₜₚ (htpy-refl (g ∘ id))            ~⟨ ·ₕₜₚ-runit (lwhisker G id) ⟩
          lwhisker G id                                        ~⟨ lwhisker-id G ⟩
          G                                                    ∎-htpy

      --      │       │      │    │  
      --      │      [K]     │   [K] 
      -- [G ·ₕₜₚ H]   │  =  [H]   │  
      --      │       │      │    │  
      --      │       │     [G]   │  
      --      │       │      │    │  
      --      f       k      f    k  
      hcomp-lconcat : {A B C : Set} → {f g h : B → C} → (G : f ~ g) → (H : g ~ h) →
                                {k i : A → B} → (K : k ~ i) →
                                hcomp (G ·ₕₜₚ H) K ~ (lwhisker G k) ·ₕₜₚ (hcomp H K)
      hcomp-lconcat {A} {B} {C} {f} {g} {h} G H {k} {i} K =
        begin-htpy
          hcomp (G ·ₕₜₚ H) K                                ~⟨⟩
          (lwhisker (G ·ₕₜₚ H) k) ·ₕₜₚ (rwhisker h K)                 ~⟨ ·ₕₜₚ-lhtpe (lwhisker-concat G H k) _ ⟩
          (lwhisker G k) ·ₕₜₚ  (lwhisker H k) ·ₕₜₚ (rwhisker h K)     ~⟨ ·ₕₜₚ-assoc (lwhisker G k) _ _ ⟩
          (lwhisker G k) ·ₕₜₚ ((lwhisker H k) ·ₕₜₚ (rwhisker h K))    ~⟨⟩
          (lwhisker G k) ·ₕₜₚ (hcomp H K)                   ∎-htpy

      -- If p : K1 ~ K2, then:
      --  k    g       k    g  
      --  │    │       │    │  
      --  │   [G]  ~   │   [G] 
      -- [K1]  │      [K2]  │  
      --  │    │       │    │  
      --  h    f       h    f  
      hcomp-lhtpe : {A B C : Set} → {h k : B → C} → {K1 K2 : h ~ k} →
                              (p : K1 ~ K2) → {f g : A → B} → (G : f ~ g) →
                              hcomp K1 G ~ hcomp K2 G
      hcomp-lhtpe {A} {B} {C} {h} {k} {K1} {K2} p {f} {g} G =
        begin-htpy
          hcomp K1 G                                 ~⟨⟩
          (lwhisker K1 f) ·ₕₜₚ (rwhisker k G)                  ~⟨ ·ₕₜₚ-lhtpe (lwhisker-lhtpe p _) _ ⟩
          (lwhisker K2 f) ·ₕₜₚ (rwhisker k G)                  ~⟨⟩
          hcomp K2 G                                 ∎-htpy

      -- If p : G1 ~ G2, then:
      --  k    g       k    g  
      --  │    │       │    │  
      --  │  [G1]  ~   │  [G2] 
      -- [K]   │      [K]   │  
      --  │    │       │    │  
      --  h    f       h    f  
      hcomp-rhtpe : {A B C : Set} → {h k : B → C} → (K : h ~ k) → {f g : A → B} →
                              {G1 G2 : f ~ g} → (p : G1 ~ G2) → hcomp K G1 ~ hcomp K G2
      hcomp-rhtpe {A} {B} {C} {h} {k} K {f} {g} {G1} {G2} p =
        begin-htpy
          hcomp K G1                                 ~⟨⟩
          (lwhisker K f) ·ₕₜₚ (rwhisker k G1)                  ~⟨ ·ₕₜₚ-rhtpe _ (rwhisker-rhtpe _ p) ⟩
          (lwhisker K f) ·ₕₜₚ (rwhisker k G2)                  ~⟨⟩
          hcomp K G2                                 ∎-htpy

  open Homotopy.Symbolic

  module BiInvertibleMaps where
    -- definition 9.2.1
    module _ where
      Is-sect-of : {A B : Set} → (f : A → B) → (g : B → A) → Set
      Is-sect-of f g = f ∘ g ~ id

      Sect : {A B : Set} → (f : A → B) → Set
      Sect {A} {B} f = Σ (B → A) (Is-sect-of f)

      Is-retraction-of : {A B : Set} → (f : A → B) → (g : B → A) → Set
      Is-retraction-of f g = g ∘ f ~ id

      Retr : {A B : Set} → (f : A → B) → Set
      Retr {A} {B} f = Σ (B → A) (Is-retraction-of f)

      -- "A is a retract of B"
      Is-retract-of : (A B : Set) → Set
      Is-retract-of A B = Σ (A → B) (λ f → Retr f)

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

    build-tpe-equiv : {A B : Set} → {f : A → B} → Is-equiv f → A ≃ B
    build-tpe-equiv {A} {B} {f} is-equiv = (f , is-equiv)

    -- example 9.2.3
    id-is-equiv : {A : Set} → Is-equiv (id {A})
    id-is-equiv {A} = ((id , λ x → refl), (id , λ x → refl))

    comp-equivs-is-equiv : {A B C : Set} → {g : B → C} → {f : A → B} → 
      Is-equiv g → Is-equiv f → Is-equiv (g ∘ f)
    comp-equivs-is-equiv {A} {B} {C} {g} {f} ((sg , Sg), (rg , Rg)) ((sf , Sf), (rf , Rf)) =
      (
        (sf ∘ sg , λ c → (ap g (Sf (sg c)) · (Sg c))) ,
        (rf ∘ rg , λ c → (ap rf (Rg (f c)) · (Rf c)))
      )

    ≃-refl : {A : Set} → A ≃ A
    ≃-refl {A} = (id , id-is-equiv)

    ≃-trans : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
    ≃-trans (f , f-eqv) (g , g-eqv) = (g ∘ f , comp-equivs-is-equiv g-eqv f-eqv)

    Is-inverse-of : {A B : Set} → (f : A → B) → (g : B → A) → Set
    Is-inverse-of {A} {B} f g = Is-sect-of f g × Is-retraction-of f g

    -- remark 9.2.6
    Has-inverse : {A B : Set} → (f : A → B) → Set
    Has-inverse {A} {B} f = Σ (B → A) (Is-inverse-of f)

    has-inverse-equiv : {A B : Set} → {f : A → B} → Has-inverse f → Is-equiv f
    has-inverse-equiv (g , FG , GF) = ((g , FG), (g , GF))

    -- proposition 9.2.7 (see diagrams/9.2.7.drawio.svg for pictorial proof)
    equiv-has-inverse : {A B : Set} → {f : A → B} → Is-equiv f → Has-inverse f
    equiv-has-inverse {A} {B} {f} ((g , G), (h , H)) =
      (g , G , (lwhisker K f) ·ₕₜₚ H)
        where
        K : g ~ h
        K = (lwhisker H g) ⁻¹ₕₜₚ ·ₕₜₚ (rwhisker h G)

    -- corollary 9.2.8
    ≃-inverse-map-for : {A B : Set} → {f : A → B} → Is-equiv f → (B → A)
    ≃-inverse-map-for ((g , _), _) = g

    ≃-inverse-map-is-equiv : {A B : Set} → {f : A → B} → (is-eqv : Is-equiv f) → Is-equiv (≃-inverse-map-for is-eqv)
    ≃-inverse-map-is-equiv {A} {B} {f} f-is-equiv@((g , gsect), (g' , g'retr)) =
      ((f , fsect), (f , gsect))
      where
        fsect : Is-sect-of g f
        fsect = Σ.snd (Σ.snd (equiv-has-inverse f-is-equiv))
    
    ≃-inverse-map-is-sect-of-original : {A B : Set} → {f : A → B} → (f-is-eqv : Is-equiv f) → Is-sect-of f (≃-inverse-map-for f-is-eqv)
    ≃-inverse-map-is-sect-of-original ((g , gsect) , _) = gsect

    ≃-inverse-map-is-retr-of-original : {A B : Set} → {f : A → B} → (f-is-eqv : Is-equiv f) → Is-retraction-of f (≃-inverse-map-for f-is-eqv)
    ≃-inverse-map-is-retr-of-original ((g , gSect) , (r , R)) =
      let
        (_ {- should equal g -} , gsect , gretr) = equiv-has-inverse ((g , gSect) , (r , R))
      in gretr

    ≃-inverse-map-is-inverse-of-original : {A B : Set} → {f : A → B} → (f-is-eqv : Is-equiv f) → Is-inverse-of f (≃-inverse-map-for f-is-eqv)
    ≃-inverse-map-is-inverse-of-original f-is-eqv =
      (≃-inverse-map-is-sect-of-original f-is-eqv , ≃-inverse-map-is-retr-of-original f-is-eqv)

    ≃-inverse : {A B : Set} → A ≃ B → B ≃ A
    ≃-inverse {A} {B} (_ , eqv) = (≃-inverse-map-for eqv , ≃-inverse-map-is-equiv eqv)

    ≃-comm : {A B : Set} → A ≃ B → B ≃ A
    ≃-comm eqv = ≃-inverse eqv

    ≃-then-iff : {A B : Set} → A ≃ B → (A ↔ B)
    ≃-then-iff {A} {B} (fwd , (bwd , _) , _) = (fwd , bwd)

    module Equivalence-Reasoning where
      infix  1 begin-≃_
      infixr 2 step-≃-∣ step-≃-⟩ step-≃-⟩⁻¹
      infix  3 _∎-≃

      begin-≃_ : {A B : Set} → (A≃B : A ≃ B) → A ≃ B
      begin-≃ A≃B = A≃B

      step-≃-∣ : (A : Set) → {B : Set} → (A ≃ B) → (A ≃ B)
      step-≃-∣ A A≃B = A≃B

      step-≃-⟩ : (A : Set) → {B C : Set} → (A ≃ B) → (B ≃ C) → (A ≃ C)
      step-≃-⟩ A A≃B B≃C = ≃-trans A≃B B≃C

      step-≃-⟩⁻¹ : (A : Set) → {B C : Set} → (B ≃ A) → (B ≃ C) → (A ≃ C)
      step-≃-⟩⁻¹ A B≃A B≃C = ≃-trans (≃-inverse B≃A) B≃C

      syntax step-≃-∣ A A≃B       =  A ≃⟨⟩ A≃B
      syntax step-≃-⟩ A A≃B B≃C   =  A ≃⟨ A≃B ⟩ B≃C
      syntax step-≃-⟩⁻¹ A B≃A B≃C =  A ≃⟨← B≃A ⟩ B≃C

      _∎-≃ : (A : Set) → A ≃ A
      A ∎-≃  =  ≃-refl
    
    -- example 9.2.9
    module _ where
      open +₀-Basic
      open EmptyBasic
      open Equivalence-Reasoning

      +₀-comm : {A B : Set} → A +₀ B ≃ B +₀ A
      +₀-comm =
        (swap-+₀ ,
          (has-inverse-equiv (
            swap-+₀ ,
            (λ { (left _) → refl ; (right _) → refl }),
            (λ { (left _) → refl ; (right _) → refl }))))

      +₀-both-≃ : {A B C D : Set} → (A ≃ C) → (B ≃ D) → (A +₀ B ≃ C +₀ D)
      +₀-both-≃ (f , (fs , fS), (fr , fR)) (g , (gs , gS), (gr , gR)) =
        (< f +₀ g > ,
          ((λ { (left c) → left (fs c) ; (right d) → right (gs d) }) , (λ { (left c) → ap left (fS c) ; (right d) → ap right (gS d) })) ,
          ((λ { (left c) → left (fr c) ; (right d) → right (gr d) }) , (λ { (left c) → ap left (fR c) ; (right d) → ap right (gR d) }))
        )

      +₀-lunit : {A : Set} → Empty +₀ A ≃ A
      +₀-lunit =
        (
          (  λ { (left emp) → absurd emp ; (right a) → a }),
          (has-inverse-equiv (
            right ,
            (λ a → refl),
            (λ { (left emp) → absurd emp ; (right a) → refl }))))

      +₀-runit : {A : Set} → A +₀ Empty ≃ A
      +₀-runit {A} = begin-≃
        A +₀ Empty     ≃⟨ +₀-comm ⟩
        Empty +₀ A     ≃⟨ +₀-lunit ⟩
        A              ∎-≃

      +₀-assoc : {A B C : Set} → (A +₀ B) +₀ C ≃ A +₀ (B +₀ C)
      +₀-assoc =
        (
          (  λ { (left (left a)) → left a ; (left (right b)) → right (left b) ; (right c) → right (right c) }),
          has-inverse-equiv (
            (λ { (left a) → left (left a) ; (right (left b)) → left (right b) ; (right (right c)) → right c }) ,
            (λ { (left a) → refl          ; (right (left b)) → refl           ; (right (right c)) → refl }) ,
            (λ { (left (left a)) → refl   ; (left (right b)) → refl           ; (right c) → refl })
          )
        )

      ×-comm : {A B : Set} → A × B ≃ B × A
      ×-comm =
        ((   λ { (a , b) → (b , a) }) ,
          has-inverse-equiv (
            (λ { (b , a) → (a , b) }) ,
            (λ { (a , b) → refl }) ,
            (λ { (b , a) → refl })
          ))

      ×-lzero : {A : Set} → Empty × A ≃ Empty
      ×-lzero = ((λ { (() , a) }) , has-inverse-equiv ((λ { () }) , (λ { () }) , (λ { (() , a) })))

      ×-rzero : {A : Set} → A × Empty ≃ Empty
      ×-rzero = ≃-trans ×-comm ×-lzero

      ×-lunit : {A : Set} → Unit × A ≃ A
      ×-lunit =
        (
          (  λ { (unit , a) → a }) ,
          has-inverse-equiv (
            (λ { a          → (unit , a) }) ,
            (λ { a          → refl }) ,
            (λ { (unit , a) → refl })
          )
        )
      
      ×-runit : {A : Set} → A × Unit ≃ A
      ×-runit = ≃-trans ×-comm ×-lunit

      ×-assoc : {A B C : Set} → (A × B) × C ≃ A × (B × C)
      ×-assoc =
        (
          (  λ { ((a , b) , c) → (a , (b , c)) }) ,
          has-inverse-equiv (
            (λ { (a , (b , c)) → ((a , b) , c) }) ,
            (λ { (a , (b , c)) → refl }) ,
            (λ { ((a , b) , c) → refl })
          )
        )

      ×-ldistr-+₀ : {A B C : Set} → A × (B +₀ C) ≃ (A × B) +₀ (A × C)
      ×-ldistr-+₀ =
        (
          (  λ { (a , left b) → left (a , b)   ; (a , right c)   → right (a , c) }) ,
          has-inverse-equiv (
            (λ { (left (a , b)) → (a , left b) ; (right (a , c)) → (a , right c) }) ,
            (λ { (left (a , b)) → refl         ; (right (a , c)) → refl }) ,
            (λ { (a , left b)   → refl         ; (a , right c)   → refl })
          )
        )
      
      ×-rdistr-+₀ : {A B C : Set} → (B +₀ C) × A ≃ (B × A) +₀ (C × A)
      ×-rdistr-+₀ =
        (
          (  λ { (left b , a) → left (b , a)   ; (right c , a)   → right (c , a) }) ,
          has-inverse-equiv (
            (λ { (left (b , a)) → (left b , a) ; (right (c , a)) → (right c , a) }) ,
            (λ { (left (b , a)) → refl         ; (right (c , a)) → refl }) ,
            (λ { (left b , a) → refl           ; (right c , a)   → refl })
          )
        )
    
    -- example 9.2.10
    module _ where
      open Σ-Basic
      open EmptyBasic
      open Equivalence-Reasoning

      Σ-lzero : {B : Empty → Set} → Σ Empty B ≃ Empty
      Σ-lzero = ((λ { (() , b) }) , has-inverse-equiv ((λ { () }) , (λ { () }) , (λ { (() , b) })))

      Σ-rzero : {A : Set} → Σ A (λ x → Empty) ≃ Empty
      Σ-rzero = ((λ { (a , ()) }) , has-inverse-equiv ((λ { () }) , (λ { () }) , (λ { (a , ()) })))

      Σ-lunit : {B : Unit → Set} → Σ Unit B ≃ B unit
      Σ-lunit =
        ((   λ { (unit , b) → b }) ,
          has-inverse-equiv (
            (λ { b          → (unit , b) }) ,
            (λ { b          → refl }) ,
            (λ { (unit , b) → refl })))
  
      Σ-runit : {A : Set} → Σ A (λ x → Unit) ≃ A
      Σ-runit =
        ((   λ { (a , unit) → a }) ,
          has-inverse-equiv (
            (λ { a          → (a , unit) }) ,
            (λ { a          → refl }) ,
            (λ { (a , unit) → refl })))

      Σ-assoc-uncurried : {A : Set} → {B : A → Set} → {C : Σ A B → Set} →
                          Σ (Σ A B) C ≃ Σ A (λ x → Σ (B x) (λ y → C (x , y)))
      Σ-assoc-uncurried =
        ((   λ { ((x , y) , c) → (x , (y , c)) }) ,
          has-inverse-equiv (
            (λ { (x , (y , c)) → ((x , y) , c) }) ,
            (λ { (x , (y , c)) → refl }) ,
            (λ { ((x , y) , c) → refl })))

      Σ-assoc-curried : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set} →
                        Σ (Σ A B) (λ w → C (Σ.fst w) (Σ.snd w)) ≃ Σ A (λ x → Σ (B x) (λ y → C x y))
      Σ-assoc-curried =
        ((   λ { ((x , y) , c) → (x , (y , c)) }) ,
          has-inverse-equiv (
            (λ { (x , (y , c)) → ((x , y) , c) }) ,
            (λ { (x , (y , c)) → refl }) ,
            (λ { ((x , y) , c) → refl })))

      Σ-ldistr-+₀ : {A : Set} → {B : A → Set} → {C : A → Set} →
                    Σ A (λ x → B x +₀ C x) ≃ (Σ A B +₀ Σ A C)
      Σ-ldistr-+₀ =
        ((   λ { (x , left b) → left (x , b)   ; (x , right c)   → right (x , c) }) ,
          has-inverse-equiv (
            (λ { (left (x , b)) → (x , left b) ; (right (x , c)) → (x , right c) }) ,
            (λ { (left (x , b)) → refl         ; (right (x , c)) → refl }) ,
            (λ { (x , left b) → refl           ; (x , right c)   → refl })))

      Σ-rdistr-+₀ : {A : Set} → {B : Set} → {C : (A +₀ B) → Set} →
                    Σ (A +₀ B) C ≃ (Σ A (λ x → C (left x)) +₀ (Σ B (λ y → C (right y))))
      Σ-rdistr-+₀ =
        ((   λ { (left x , c) → left (x , c)   ; (right y , c)   → right (y , c) }) ,
          has-inverse-equiv (
            (λ { (left (x , c)) → (left x , c) ; (right (y , c)) → (right y , c) }) ,
            (λ { (left (x , c)) → refl         ; (right (y , c)) → refl }) ,
            (λ { (left x , c) → refl           ; (right y , c)   → refl })))

  open ≡-Basic

  -- definition 9.3.1
  Eq-Σ : {A : Set} → {B : A → Set} → (Σ A B) → (Σ A B) → Set
  Eq-Σ {A} {B} (a1 , b1) (a2 , b2) = Σ (a1 ≡ a2) (λ α → tr B α b1 ≡ b2)

  module _ where
    open ≡-Reasoning
    open Equivalence

    -- lemma 9.3.2
    Eq-Σ-refl : {A : Set} → {B : A → Set} → (s : Σ A B) → Eq-Σ s s
    Eq-Σ-refl {A} {B} (a , b) = (refl , refl)

    -- definition 9.3.3
    pair-eq-Eq-Σ : {A : Set} → {B : A → Set} → {s t : Σ A B} → (s ≡ t) → Eq-Σ s t
    pair-eq-Eq-Σ {A} {B} {s} {.s} refl = Eq-Σ-refl s

    eq-pair : {A : Set} → {B : A → Set} → (s t : Σ A B) → Eq-Σ s t → s ≡ t
    eq-pair {A} {B} (a1 , b1) (a2 , b2) (refl , refl) = refl

    -- theorem 9.3.4
    pair-eq-Eq-Σ-is-equiv : {A : Set} → {B : A → Set} → {s t : Σ A B} → Is-equiv (pair-eq-Eq-Σ {A} {B} {s} {t})
    pair-eq-Eq-Σ-is-equiv {A} {B} {s@(a1 , b1)} {t} =
      has-inverse-equiv
        (eq-pair s t , S , R)
      where
        S : Is-sect-of pair-eq-Eq-Σ (eq-pair s t)
        S = by-inductions t
          where
            by-inductions : (t' : Σ A B) → (x : Eq-Σ s t') → pair-eq-Eq-Σ (eq-pair s t' x) ≡ x
            by-inductions (a2 , b2) (refl , refl) = refl

        R : Is-retraction-of pair-eq-Eq-Σ (eq-pair s t)
        R refl = refl

    open Equivalence.Symbolic
    pair-eq-≃-Eq-Σ : {A : Set} → {B : A → Set} → {s t : Σ A B} → (s ≡ t) ≃ Eq-Σ s t
    pair-eq-≃-Eq-Σ {A} {B} {s} {t} = (pair-eq-Eq-Σ , pair-eq-Eq-Σ-is-equiv)

  open ≡-Basic
  open ≡-Reasoning
  open Homotopy
  open Homotopy.Symbolic
  open HomotopyGroupoidSymbolic
  open Equivalence
  open Equivalence.Symbolic
  open Equivalence-Reasoning

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
          p · (p ⁻¹ · q) ≡⟨ ·-unassoc p (p ⁻¹) q ⟩
          p · p ⁻¹ · q   ≡⟨ ap (λ e → e · q) (·-rinv p) ⟩
          refl · q       ≡⟨⟩
          q              ∎

        retract-eq : inverseMap ∘ (_·_ p) ~ id
        retract-eq q = begin
          p ⁻¹ · (p · q) ≡⟨ ·-unassoc (p ⁻¹) p q ⟩
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
          tr B p (tr B (p ⁻¹) by)       ≡⟨← tr-concat (p ⁻¹) _ _ ⟩
          tr B (p ⁻¹ · p) by            ≡⟨ ap (λ e → tr B e by) (·-linv p) ⟩
          tr B refl by                  ≡⟨⟩
          id by                         ∎

        retract-eq : inverseMap ∘ (tr B p) ~ id
        retract-eq by = begin
          (inverseMap ∘ (tr B p)) by    ≡⟨⟩
          tr B (p ⁻¹) (tr B p by)       ≡⟨← tr-concat p _ _ ⟩
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

    Inhabited-≄-Empty : {A : Set} → (a : A) → A ≄ Empty
    Inhabited-≄-Empty a (f , _) = absurd (f a)

    Nat≃+Unit-then-Nat≃ : {A : Set} → (forward : Nat → A +₀ Unit) → Has-inverse forward → Σ (Nat → A) Has-inverse
    Nat≃+Unit-then-Nat≃ {A} forward (backward , Sect , Retr) =
      (forward' , (backward' , forward'∘backward'~id , backward'∘forward'~id))
      where open Lt-Nat.Symbolic
            open Leq-Nat.Symbolic

            pointToEliminate = backward (right unit)

            forward-is-unit-only-at-pointToEliminate : (n : Nat) → (forward n ≡ right unit) → (n ≡ pointToEliminate)
            forward-is-unit-only-at-pointToEliminate n fn≡unit =
              begin
                n                      ≡⟨← (Retr n) ⟩
                backward (forward n)   ≡⟨ ap backward (fn≡unit) ⟩
                backward (right unit)  ≡⟨⟩
                pointToEliminate       ∎
            
            backward-left-is-not-pointToEliminate : (a : A) → pointToEliminate ≢ backward (left a)
            backward-left-is-not-pointToEliminate a pt≡bla =
              let ru≡la = begin
                    (right unit)                     ≡⟨← (Sect (right unit)) ⟩
                    forward (backward (right unit))  ≡⟨ ap forward pt≡bla ⟩
                    forward (backward (left a))      ≡⟨ Sect (left a) ⟩
                    left a                           ∎
              in Eq-Copr.left-neq-right (inverse ru≡la)

            extract-a-from-forward-cases : (n : Nat) → (n≠pt : n ≢ pointToEliminate) → (copr : A +₀ Unit) → (forward n ≡ copr) → A
            extract-a-from-forward-cases n n≠pt =
              ind-+₀ {A} {Unit} (λ copr → forward n ≡ copr → A)
                (λ a _ → a)
                (λ { unit eq → absurd (n≠pt (forward-is-unit-only-at-pointToEliminate n eq)) })
            extract-a-from-forward : (n : Nat) → (n ≢ pointToEliminate) → A
            extract-a-from-forward n n≠pt = extract-a-from-forward-cases n n≠pt (forward n) refl

            extract-a-from-forward-eq-forward : (n : Nat) → {n≠pt : n ≢ pointToEliminate} → left (extract-a-from-forward n n≠pt) ≡ forward n
            extract-a-from-forward-eq-forward n {n≠pt} =
              ind-+₀ {A} {Unit} (λ copr → forward n ≡ copr → left (extract-a-from-forward n n≠pt) ≡ forward n)
                (λ a eq → begin
                  left (extract-a-from-forward n n≠pt)                            ≡⟨⟩
                  left (extract-a-from-forward-cases n n≠pt (forward n) refl)     ≡⟨ ap left (transport-equality-fn (forward n) (extract-a-from-forward-cases n n≠pt) eq) ⟩
                  left (extract-a-from-forward-cases n n≠pt (left a) eq)          ≡⟨⟩
                  left a                                                          ≡⟨← eq ⟩
                  forward n                                                       ∎
                )
                (λ { unit eq → absurd (n≠pt (forward-is-unit-only-at-pointToEliminate n eq)) })
                (forward n) refl
              where
                transport-equality-fn : {X P : Set} → (x : X) → (depfn : (z : X) → (x ≡ z) → P) → {y : X} → (q : x ≡ y) → depfn x refl ≡ depfn y q
                transport-equality-fn x d refl = refl

            forward'-cases : (n : Nat) → ((n < pointToEliminate) +₀ (pointToEliminate ≤ n)) → A
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

            backward'-cases : (res : Nat) → ((res ≤ pointToEliminate) +₀ (pointToEliminate < res)) → Nat
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
              ; (right bla>pt) →
                  let (predbla , succ-predbla) = Lt-Nat.gt-something-then-exists-pred (backward (left a)) {pointToEliminate} bla>pt
                      b'a≡predOrZero-bla = backward'≡predOrZero∘backward∘left-if-bla>pt a bla>pt
                      predOrZero-bla≥pt = Lt-Nat.lt-then-leq-predOrZero pointToEliminate (backward (left a)) bla>pt
                      predOrZero-bla<pt = tr (λ e → e < pointToEliminate) b'a≡predOrZero-bla b'a<pt
                  in absurd (Σ.fst (Lt-Nat.lt-iff-not-flip-leq (NatBasic.predOrZero (backward (left a))) pointToEliminate) predOrZero-bla<pt predOrZero-bla≥pt)
              }
            backward'≥pt-then-backward∘left>pt : (a : A) → (pointToEliminate ≤ backward' a) → (pointToEliminate < backward (left a))
            backward'≥pt-then-backward∘left>pt a b'a≥pt =
              Lt-Nat.by-comparing-leq-or-gt (backward (left a)) pointToEliminate λ {
                (left bla≤pt) →
                  let b'a≡bla = backward'≡backward∘left-if-bla≤pt a bla≤pt
                      bla≥pt = tr (λ e → pointToEliminate ≤ e) b'a≡bla b'a≥pt
                  in Lt-Nat.leq-and-neq-then-lt pointToEliminate (backward (left a)) bla≥pt (backward-left-is-not-pointToEliminate a)
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
              Eq-Copr.+₀-left-inj {A} {Unit} (
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
    open Homotopy.Reasoning
    
    is-equiv-preserved-by-homotopy : {A B : Set} → {f g : A → B} → f ~ g → Is-equiv f → Is-equiv g
    is-equiv-preserved-by-homotopy {A} {B} {f} {g} FG ((s , S), (r , R)) =
      ((s , (lwhisker (FG ⁻¹ₕₜₚ) s ·ₕₜₚ S)),
        (r , (rwhisker r (FG ⁻¹ₕₜₚ) ·ₕₜₚ R)))

    homotope-implies-is-equiv-iff : {A B : Set} → {f g : A → B} → f ~ g → Is-equiv f ↔ Is-equiv g
    homotope-implies-is-equiv-iff {A} {B} {f} {g} FG =
      (is-equiv-preserved-by-homotopy FG , is-equiv-preserved-by-homotopy (FG ⁻¹ₕₜₚ))

    sect-with-retr-is-retr : {A B : Set} → {f : A → B} → {g : B → A} → Is-sect-of f g → (Σ _ (Is-retraction-of f)) → Is-retraction-of f g
    sect-with-retr-is-retr {A} {B} {f} {g} gsect (r , R) = Σ.snd (Σ.snd (equiv-has-inverse ((g , gsect), (r , R))))

    homotopic-equiv-has-homotopic-inverses : {A B : Set} → {e e' : A → B} → (ee : Is-equiv e) → (ee' : Is-equiv e') → e ~ e' →
                                              ≃-inverse-map-for ee ~ ≃-inverse-map-for ee'
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
    open Homotopy.Reasoning

    -- exercise 9.4.a
    section-of-first-map-commutes-inverted-triangle : {A B X : Set} →
                                                      {h : A → B} → {f : A → X} → (g : B → X) → (H : f ~ g ∘ h) →
                                                      ((s , S) : Sect h) → g ~ f ∘ s
    section-of-first-map-commutes-inverted-triangle {A} {B} {X} {h} {f} g H (s , S) =
      begin-htpy
        g             ~⟨⟩
        g ∘ id        ~⟨ rwhisker g (S ⁻¹ₕₜₚ) ⟩
        g ∘ (h ∘ s)   ~⟨⟩
        g ∘ h ∘ s     ~⟨ lwhisker (H ⁻¹ₕₜₚ) s ⟩
        f ∘ s         ∎-htpy

    Sect-comp-then-Sect-latter : {A B X : Set} →
                                 (h : A → B) → {f : A → X} → (g : B → X) → (H : f ~ g ∘ h) →
                                 ((fs , fS) : Sect f) → Sect g
    Sect-comp-then-Sect-latter {A} {B} {X} h {f} g H (fs , fS) =
      (h ∘ fs , (begin-htpy
        g ∘ (h ∘ fs)   ~⟨⟩
        g ∘ h ∘ fs     ~⟨ lwhisker (H ⁻¹ₕₜₚ) fs ⟩
        f ∘ fs         ~⟨ fS ⟩
        id             ∎-htpy
      ))

    comp-of-maps-with-sections-has-section : {A B X : Set} →
                                              {h : A → B} → {f : A → X} → {g : B → X} → (H : f ~ g ∘ h) →
                                              ((hs , hS) : Sect h) → ((gs , gS) : Sect g) → Sect f
    comp-of-maps-with-sections-has-section {A} {B} {X} {h} {f} {g} H (hs , hS) (gs , gS) =
      (hs ∘ gs , (begin-htpy
        f ∘ (hs ∘ gs)        ~⟨ lwhisker H (hs ∘ gs) ⟩
        g ∘ h ∘ (hs ∘ gs)    ~⟨ rwhisker g (lwhisker hS gs) ⟩
        g ∘ id ∘ gs          ~⟨⟩
        g ∘ gs               ~⟨ gS ⟩
        id                   ∎-htpy
      ))

    Sect-former-then-Sect-comp-biimpl-Sect-latter : {A B X : Set} →
                                                 {h : A → B} → {f : A → X} → (g : B → X) → (H : f ~ g ∘ h) →
                                                 Sect h → Sect f ↔ Sect g
    Sect-former-then-Sect-comp-biimpl-Sect-latter {A} {B} {X} {h} {f} g H h-Sect =
      (Sect-comp-then-Sect-latter h g H , comp-of-maps-with-sections-has-section {A} {B} {X} {h} {f} {g} H h-Sect)

    -- exercise 9.4.b ; this is dual to (a)
    retr-of-second-map-commutes-inverted-triangle : {A B X : Set} →
                                                    (h : A → B) → {f : A → X} → {g : B → X} → (H : f ~ g ∘ h) →
                                                    ((gr , gR) : Retr g) → h ~ gr ∘ f
    retr-of-second-map-commutes-inverted-triangle {A} {B} {X} h {f} {g} H (gr , gR) =
      begin-htpy
        h              ~⟨⟩
        id ∘ h         ~⟨ lwhisker (gR ⁻¹ₕₜₚ) h ⟩
        (gr ∘ g) ∘ h   ~⟨⟩
        gr ∘ g ∘ h     ~⟨ rwhisker gr (H ⁻¹ₕₜₚ) ⟩
        gr ∘ f         ∎-htpy
    
    Retr-comp-then-Retr-former : {A B X : Set} →
                                  (h : A → B) → {f : A → X} → (g : B → X) → (H : f ~ g ∘ h) →
                                  ((fr , fR) : Retr f) → Retr h
    Retr-comp-then-Retr-former {A} {B} {X} h {f} g H (fr , fR) =
      (fr ∘ g , (begin-htpy
        (fr ∘ g) ∘ h    ~⟨⟩
        fr ∘ (g ∘ h)    ~⟨ rwhisker fr (H ⁻¹ₕₜₚ) ⟩
        fr ∘ f          ~⟨ fR ⟩
        id              ∎-htpy
      ))
    
    comp-of-maps-with-retr-has-retr : {A B X : Set} →
                                      {h : A → B} → {f : A → X} → {g : B → X} → (H : f ~ g ∘ h) →
                                      ((hr , hR) : Retr h) → ((gr , gR) : Retr g) → Retr f
    comp-of-maps-with-retr-has-retr {A} {B} {X} {h} {f} {g} H (hr , hR) (gr , gR) =
      (hr ∘ gr , (begin-htpy
        (hr ∘ gr) ∘ f         ~⟨ rwhisker (hr ∘ gr) H ⟩
        (hr ∘ gr) ∘ (g ∘ h)   ~⟨ rwhisker hr (lwhisker gR h) ⟩
        hr ∘ h                ~⟨ hR ⟩
        id                    ∎-htpy
      ))

    -- exercise 9.4.c
    former-and-comp-are-equivs-then-latter-is-equiv : {A B X : Set} →
                                                      {h : A → B} → {f : A → X} → {g : B → X} → (H : f ~ g ∘ h) →
                                                      Is-equiv h → Is-equiv f → Is-equiv g
    former-and-comp-are-equivs-then-latter-is-equiv {A} {B} {X} {h} {f} {g} H h-eqv f-eqv =
      let
        (h⁻¹ , h⁻¹-eqv) = ≃-inverse (h , h-eqv)
        fh⁻¹~g : f ∘ h⁻¹ ~ g
        fh⁻¹~g =
          begin-htpy
            f ∘ h⁻¹         ~⟨ lwhisker H (h⁻¹) ⟩
            g ∘ h ∘ h⁻¹     ~⟨ rwhisker g (≃-inverse-map-is-sect-of-original h-eqv) ⟩
            g ∘ id          ~⟨⟩
            g               ∎-htpy
      in
        is-equiv-preserved-by-homotopy fh⁻¹~g (comp-equivs-is-equiv f-eqv h⁻¹-eqv)

    latter-and-comp-are-equivs-then-former-is-equiv : {A B X : Set} →
                                                      (h : A → B) → {f : A → X} → {g : B → X} → (H : f ~ g ∘ h) →
                                                      Is-equiv g → Is-equiv f → Is-equiv h
    latter-and-comp-are-equivs-then-former-is-equiv {A} {B} {X} h {f} {g} H g-eqv f-eqv =
      let
        (g⁻¹ , g⁻¹-eqv) = ≃-inverse (g , g-eqv)
        g⁻¹f~h : g⁻¹ ∘ f ~ h
        g⁻¹f~h =
          begin-htpy
            g⁻¹ ∘ f         ~⟨ rwhisker g⁻¹ H ⟩
            g⁻¹ ∘ (g ∘ h)   ~⟨ lwhisker (≃-inverse-map-is-retr-of-original g-eqv) h ⟩
            id ∘ h          ~⟨⟩
            h               ∎-htpy
      in
        is-equiv-preserved-by-homotopy g⁻¹f~h (comp-equivs-is-equiv g⁻¹-eqv f-eqv)
    
    sect-of-equiv-is-equiv : {A B : Set} → {f : A → B} → (((s , S) , _) : Is-equiv f) → Is-equiv s
    sect-of-equiv-is-equiv ((s , S) , (r , R)) = ≃-inverse-map-is-equiv ((s , S) , (r , R))

    retr-of-equiv-is-equiv : {A B : Set} → {f : A → B} → ((_ , (r , R)) : Is-equiv f) → Is-equiv r
    retr-of-equiv-is-equiv eqv@(_ , (r , R)) =
      -- We use id ~ r ∘ f and that id and f are equivalences
      former-and-comp-are-equivs-then-latter-is-equiv
        (R ⁻¹ₕₜₚ) eqv id-is-equiv

    -- ↔-lemmas which will be useful later on
    latter-is-equiv-then-comp-is-equiv-iff-former-is-equiv : {A B X : Set} → (h : A → B) → {f : A → X} → {g : B → X} →
                                                             (H : f ~ g ∘ h) → Is-equiv g → Is-equiv f ↔ Is-equiv h
    latter-is-equiv-then-comp-is-equiv-iff-former-is-equiv {A} {B} {X} h {f} {g} H g-eqv =
      (
        latter-and-comp-are-equivs-then-former-is-equiv h H g-eqv ,
        (λ f-eqv →
          is-equiv-preserved-by-homotopy (H ⁻¹ₕₜₚ) (comp-equivs-is-equiv g-eqv f-eqv)
        )
      )

  -- exercise 9.5
  module _ where
    -- exercise 9.5.a
    swap-ΣΣ-fn : {A B : Set} → {C : A → B → Set} → Σ A (λ a → Σ B (λ b → C a b)) → Σ B (λ b → Σ A (λ a → C a b))
    swap-ΣΣ-fn (a , (b , c)) = (b , (a , c))
    swap-ΣΣ : {A B : Set} → {C : A → B → Set} → Σ A (λ a → Σ B (λ b → C a b)) ≃ Σ B (λ b → Σ A (λ a → C a b))
    swap-ΣΣ =
      (
        swap-ΣΣ-fn ,
        has-inverse-equiv (
          swap-ΣΣ-fn ,
          (λ { (b , (a , c)) → refl }) ,
          (λ { (a , (b , c)) → refl })
        )
      )

    -- exercise 9.5.b
    swap-ΣΣ-families-fn : {A : Set} → {B C : A → Set} →
                          Σ (Σ A B) (λ u → C (Σ.fst u)) → Σ (Σ A C) (λ v → B (Σ.fst v))
    swap-ΣΣ-families-fn ((a , b) , c) = ((a , c) , b)
    swap-ΣΣ-families : {A : Set} → {B C : A → Set} →
                        Σ (Σ A B) (λ u → C (Σ.fst u)) ≃ Σ (Σ A C) (λ v → B (Σ.fst v))
    swap-ΣΣ-families =
      (
        swap-ΣΣ-families-fn ,
        has-inverse-equiv (
          swap-ΣΣ-families-fn ,
          (λ { ((a , c) , b) → refl }) ,
          (λ { ((a , b) , c) → refl })
        )
      )

  -- We cannot yet prove the equivalence of this function
  flipDependentFn : {A B : Set} → {C : (x : A) → (y : B) → Set} → ((x : A) → (y : B) → C x y) → ((y : B) → (x : A) → C x y)
  flipDependentFn f y x = f x y

  flipDependentBiimpl : {A B : Set} → {C : (x : A) → (y : B) → Set} → ((x : A) → (y : B) → C x y) ↔ ((y : B) → (x : A) → C x y)
  flipDependentBiimpl = (flipDependentFn , flipDependentFn)

  -- exercise 9.6
  module _ where
    open +₀-Basic

    +₀-functorial-id : {A B : Set} → (< id {A} +₀ id {B} >) ~ id {A +₀ B}
    +₀-functorial-id = λ { (left a) → refl ; (right b) → refl }

    +₀-functorial-comp : {A A' A'' B B' B'' : Set} →
                          (f : A → A') → (f' : A' → A'') → (g : B → B') → (g' : B' → B'') →
                          <(f' ∘ f) +₀ (g' ∘ g)> ~ (< f' +₀ g' > ∘ < f +₀ g >)
    +₀-functorial-comp f f' g g' = λ { (left a) → refl ; (right b) → refl }

    +₀-homotopy : {A A' B B' : Set} →
                  {f f' : A → A'} → {g g' : B → B'} → (H : f ~ f') → (K : g ~ g') →
                  < f +₀ g > ~ < f' +₀ g' >
    +₀-homotopy H K = λ { (left a) → ap left (H a) ; (right b) → ap right (K b) }

    +₀-equiv : {A A' B B' : Set} →
                {f : A → A'} → {g : B → B'} → Is-equiv f → Is-equiv g →
                Is-equiv < f +₀ g >
    +₀-equiv {A} {A'} {B} {B'} {f} {g} ((fs , fS) , (fr , fR)) ((gs , gS) , (gr , gR)) =
      (
        (< fs +₀ gs > , λ { (left a) → ap left (fS a) ; (right b) → ap right (gS b) }),
        (< fr +₀ gr > , λ { (left a) → ap left (fR a) ; (right b) → ap right (gR b) })
      )

  -- exercise 9.7
  module _ where
    <_×₀_> : {A B A' B' : Set} → (A → A') → (B → B') → (A × B) → (A' × B')
    < f ×₀ g > (a , b) = (f a , g b)

    ×₀-functorial-id : {A B : Set} → (< id {A} ×₀ id {B} >) ~ id {A × B}
    ×₀-functorial-id = λ { (a , b) → refl }

    ×₀-functorial-comp : {A A' A'' B B' B'' : Set} →
                          (f : A → A') → (f' : A' → A'') → (g : B → B') → (g' : B' → B'') →
                          <(f' ∘ f) ×₀ (g' ∘ g)> ~ (< f' ×₀ g' > ∘ < f ×₀ g >)
    ×₀-functorial-comp f f' g g' = λ { (a , b) → refl }

    ×₀-homotopy : {A A' B B' : Set} →
                  {f f' : A → A'} → {g g' : B → B'} → (H : f ~ f') → (K : g ~ g') →
                  < f ×₀ g > ~ < f' ×₀ g' >
    ×₀-homotopy {A} {A'} {B} {B'} {f} {f'} {g} {g'} H K =
      λ { (a , b) → 
        begin
          < f ×₀ g > (a , b)   ≡⟨⟩
          (f a , g b)          ≡⟨ ap2 (λ x y → (x , y)) (H a) (K b) ⟩
          (f' a , g' b)        ≡⟨⟩
          < f' ×₀ g' > (a , b) ∎
      }

    fst-×₀-eq-left-fst : {A A' B B' : Set} → {f : A → A'} → {g : B → B'} → (t : A × B) →
                        Σ.fst (< f ×₀ g > t) ≡ f (Σ.fst t)
    fst-×₀-eq-left-fst (a , b) = refl

    snd-×₀-eq-right-snd : {A A' B B' : Set} → {f : A → A'} → {g : B → B'} → (t : A × B) →
                         Σ.snd (< f ×₀ g > t) ≡ g (Σ.snd t)
    snd-×₀-eq-right-snd (a , b) = refl

    ×₀-equiv-then-conditionally-equivs : {A A' B B' : Set} →
                                         {f : A → A'} → {g : B → B'} → Is-equiv < f ×₀ g > →
                                         (B' → Is-equiv f) × (A' → Is-equiv g)
    ×₀-equiv-then-conditionally-equivs {A} {A'} {B} {B'} {f} {g} eqv =
      let
        f×₀g = < f ×₀ g >
        (f×₀g⁻¹ , invS , invR) = equiv-has-inverse eqv
        f⁻¹-at = λ (b' : B') (a' : A') → Σ.fst (f×₀g⁻¹ (a' , b'))
        g⁻¹-at = λ (a' : A') (b' : B') → Σ.snd (f×₀g⁻¹ (a' , b'))

        f⁻¹-is-sectionof-f = λ (b' : B') (a' : A') → begin
          f (f⁻¹-at b' a')                   ≡⟨⟩
          f (Σ.fst (f×₀g⁻¹ (a' , b')))       ≡⟨← fst-×₀-eq-left-fst (f×₀g⁻¹ (a' , b')) ⟩
          Σ.fst (f×₀g (f×₀g⁻¹ (a' , b')))    ≡⟨ ap Σ.fst (invS (a' , b')) ⟩
          Σ.fst (a' , b')                    ≡⟨⟩
          a'                                 ∎
        g⁻¹-is-sectionof-g = λ (a' : A') (b' : B') → begin
          g (g⁻¹-at a' b')                   ≡⟨⟩
          g (Σ.snd (f×₀g⁻¹ (a' , b')))       ≡⟨← snd-×₀-eq-right-snd (f×₀g⁻¹ (a' , b')) ⟩
          Σ.snd (f×₀g (f×₀g⁻¹ (a' , b')))    ≡⟨ ap Σ.snd (invS (a' , b')) ⟩
          Σ.snd (a' , b')                    ≡⟨⟩
          b'                                 ∎
      in
      (
        (λ b' →
          has-inverse-equiv (
            f⁻¹-at b' ,
            f⁻¹-is-sectionof-f b' ,
            (λ a → begin
              f⁻¹-at b' (f a)                              ≡⟨⟩
              Σ.fst (f×₀g⁻¹ (f a , b'))                    ≡⟨← ap (λ x → Σ.fst (f×₀g⁻¹ ((f a) , x))) (g⁻¹-is-sectionof-g (f a) b') ⟩
              Σ.fst (f×₀g⁻¹ (f a , g (g⁻¹-at (f a) b')))   ≡⟨⟩
              Σ.fst (f×₀g⁻¹ (f×₀g (a , g⁻¹-at (f a) b')))  ≡⟨ ap Σ.fst (invR (a , _)) ⟩
              Σ.fst (a , g⁻¹-at (f a) b')                  ≡⟨⟩
              a                                            ∎
            )
          )
        ),
        (λ a' →
          has-inverse-equiv (
            g⁻¹-at a' ,
            g⁻¹-is-sectionof-g a' ,
            (λ b → begin
              g⁻¹-at a' (g b)                               ≡⟨⟩
              Σ.snd (f×₀g⁻¹ (a' , g b))                     ≡⟨← ap (λ x → Σ.snd (f×₀g⁻¹ (x , g b))) (f⁻¹-is-sectionof-f (g b) a') ⟩
              Σ.snd (f×₀g⁻¹ (f (f⁻¹-at (g b) a') , g b))    ≡⟨⟩
              Σ.snd (f×₀g⁻¹ (f×₀g (f⁻¹-at (g b) a' , b)))   ≡⟨ ap Σ.snd (invR (_ , b)) ⟩
              Σ.snd (f⁻¹-at (g b) a' , b)                   ≡⟨⟩
              b                                             ∎
            )
          )
        )
      )

    conditionally-equivs-then-×₀-equiv : {A A' B B' : Set} →
                                         {f : A → A'} → {g : B → B'} → (B' → Is-equiv f) → (A' → Is-equiv g) →
                                         Is-equiv < f ×₀ g >
    conditionally-equivs-then-×₀-equiv {A} {A'} {B} {B'} {f} {g} f-cond-eqv g-cond-eqv =
      let
        f⁻¹×₀g⁻¹ =
          (λ { (a' , b') → 
            let (f⁻¹ , _ , _) = equiv-has-inverse (f-cond-eqv b')
                (g⁻¹ , _ , _) = equiv-has-inverse (g-cond-eqv a')
            in (f⁻¹ a' , g⁻¹ b')
          })
      in
        has-inverse-equiv (
          f⁻¹×₀g⁻¹ ,
          (λ { (a' , b') → 
            let (f⁻¹ , f⁻¹-S , _) = equiv-has-inverse (f-cond-eqv b')
                (g⁻¹ , g⁻¹-S , _) = equiv-has-inverse (g-cond-eqv a')
            in begin
              < f ×₀ g > (f⁻¹×₀g⁻¹ (a' , b'))  ≡⟨⟩
              (f (f⁻¹ a') , g (g⁻¹ b'))        ≡⟨ ap2 (λ x y → (x , y)) (f⁻¹-S a') (g⁻¹-S b') ⟩
              (a' , b')                        ∎
          }),
          (λ { (a , b) → 
            let (f⁻¹ , _ , f⁻¹-Retr) = equiv-has-inverse (f-cond-eqv (g b))
                (g⁻¹ , _ , g⁻¹-Retr) = equiv-has-inverse (g-cond-eqv (f a))
            in begin
              f⁻¹×₀g⁻¹ (< f ×₀ g > (a , b))  ≡⟨⟩
              (f⁻¹ (f a) , g⁻¹ (g b))        ≡⟨ ap2 (λ x y → (x , y)) (f⁻¹-Retr a) (g⁻¹-Retr b) ⟩
              (a , b)                        ∎
          })
        )

  -- TODO: exercise 9.8
  -- TODO: exercise 9.9
