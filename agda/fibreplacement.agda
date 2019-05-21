{-# OPTIONS --rewriting #-}
module fibreplacement where

open import prelude
open import interval
open import cofprop
open import fibrations
open import wtypesred
open import hcomp-coe
open import cofreplacement

open triv-cofibration public

module _ {A B : Set} (f : A → B) where

  data FRConstr : B → Set where
    dom : (a : A) → FRConstr (f a)
    fcomp : (r : Int) (p : Int → B) (φ : CofProp) (s t : Int) → ∥ t ≡ O ⊎ r ≡ s ∥ → FRConstr (p s)

  data FcompArity (r : Int) (p : Int → B) (φ : CofProp) : B → Set where
    fcompArg : (i : Int) → ∥ [ φ ] ⊎ (r ≡ i) ∥ → FcompArity r p φ (p i)

  FRPoly : IxPoly B
  FRPoly = record
    { Constr = FRConstr
    ; Arity = λ
      { (dom a) _ → ∅
      ; (fcomp r p φ s t w) → FcompArity r p φ
      }
    ; Red = λ
      { (dom a) → O ≈I
      ; (fcomp r p φ s t w) → φ ∨ t ≈I
      }
    ; ev = λ {b} → λ
      { (dom a) → O≠I
      ; (fcomp r p φ s t w) →
        let
          t≡ICase : t ≡ I → ∥ t ≡ O ⊎ r ≡ s ∥ → FcompArity r p φ (p s)
          t≡ICase t≡I =
            ∥⊎∥-rec uip uip
              (λ {refl → O≠I t≡I})
              (λ {refl → fcompArg r ∣ inr refl ∣})
              (λ {refl refl → O≠I t≡I})
        in
          ∨-rec φ (t ≈I)
            (λ u → fcompArg s ∣ inl u ∣)
            (λ t≡I → t≡ICase t≡I w)
            (λ u t≡I →
              ∥∥-elim (λ w → fcompArg s ∣ inl u ∣ ≡ t≡ICase t≡I w)
                (λ
                  { (inl refl) → O≠I t≡I
                  ; (inr refl) → cong (fcompArg s) (trunc _ _)
                  })
                (λ _ _ → uipImp)
                w)
      }
    }

  FR : B → Set
  FR b = IxWR FRPoly b

  FRIsFib : isFib FR
  FRIsFib r p φ h c₀ =
    record
    { comp = λ s →
      ( joined s O ∣ inl refl ∣
      , λ u →
        symm (ixred FRPoly (fcomp r p φ s O ∣ inl refl ∣) _ ∣ inl u ∣)
      )
    ; cap =
      ( path
        (λ t → joined r t ∣ inr refl ∣)
        (cong (joined r O) (trunc _ _))
        (ixred FRPoly (fcomp r p φ r I ∣ inr refl ∣) _ ∣ inr refl ∣)
      , λ t u → symm (ixred FRPoly (fcomp r p φ r t ∣ inr refl ∣) _ ∣ inl u ∣)
      )

    }
    where
    box : (i : Int) → ∥ [ φ ] ⊎ (r ≡ i) ∥ → IxWR FRPoly (p i)
    box i = ∥∥-rec _
      (λ
        { (inl u) → h u i
        ; (inr refl) → c₀ .fst
        })
      (λ
        { (inl u) (inl u') → cong (λ y → h y i) (cofIsProp φ u u')
        ; (inl u) (inr refl) → c₀ .snd u
        ; (inr refl) (inl u') → symm (c₀ .snd u')
        ; (inr refl) (inr refl) → refl
        })

    joined : (s t : Int) → ∥ t ≡ O ⊎ r ≡ s ∥ → IxWR FRPoly (p s)
    joined s t ⊔ =
      ixsup FRPoly (fcomp r p φ s t ⊔) (λ {._ (fcompArg i w) → box i w})

  quot : A → Σ B FR
  quot a = (_ , ixsup FRPoly (dom a) (λ _ → ∅-rec))

  quotIsTrivCofibration : triv-cofibration quot
  quotIsTrivCofibration = record
    { j = λ X χ quotCase → uncurry
      (IxWR-elim _ _
        (λ
          { (dom a) v _ →
            subst
              (λ v' → X (f a , ixsup _ (dom a) v'))
              (funext λ _ → funext ∅-elim)
              (quotCase a)
          ; (fcomp r p φ s t w) box boxrec →
            joined X χ r p φ box boxrec s t w 
          })
        (λ
          { (dom a) _ _ O≡I → O≠I O≡I
          ; (fcomp r p φ s t w) box boxrec →
            boundary X χ r p φ box boxrec s t w
          }))
    ; upper-tri = λ X χ quotCase a →
      cong
        (λ p → subst (λ v' → X (f a , ixsup _ (dom a) v')) p (quotCase a))
        (uip (funext λ _ → funext ∅-elim) refl)
    }
    where
    module _ (X : Σ B FR → Set) (χ : isFib X)
      (r : Int) (p : Int → B) (φ : CofProp)
      (box : (b : B) → FcompArity r p φ b → FR b)
      (boxrec : (b : B) (w' : FcompArity r p φ b) → X (b , box b w'))
      where

      fcompTerm : (s t : Int) → ∥ t ≡ O ⊎ r ≡ s ∥ → _
      fcompTerm s t w = ixsup _ (fcomp r p φ s t w) box

      fixTube : [ φ ] → (j : Int) → X (p r , fcompTerm r j ∣ inr refl ∣)
      fixTube u j =
        subst (curry X (p r))
          (symm (ixred _ (fcomp r p φ r j ∣ inr refl ∣) box ∣ inl u ∣))
          (boxrec (p r) (fcompArg r ∣ inl u ∣))

      fixBase : _ [ φ ↦ fixTube ◆ I ]
      fixBase =
        ( subst (curry X (p r))
          (symm (ixred _ (fcomp r p φ r I ∣ inr refl ∣) box ∣ inr refl ∣))
          (boxrec (p r) (fcompArg r ∣ inr refl ∣))
        , λ u →
          adjustSubstEq (curry X (p r))
            (cong (λ v → box (p r) (fcompArg r v)) (trunc _ _)) refl
            (symm (ixred _ (fcomp r p φ r I ∣ inr refl ∣) box ∣ inl u ∣))
            (symm (ixred _ (fcomp r p φ r I ∣ inr refl ∣) box ∣ inr refl ∣))
            (trans
              (congdep (λ v → boxrec (p r) (fcompArg r v)) (trunc ∣ inl u ∣ ∣ inr refl ∣))
              (symm
                (appCong
                  (subst-cong-assoc (curry X (p r)) (λ v → box (p r) (fcompArg r v))
                    (trunc ∣ inl u ∣ ∣ inr refl ∣)))))
        )

      fix =
        strictifyFib X χ I
          (λ j → p r , ixsup _ (fcomp r p φ r j ∣ inr refl ∣) box)
          φ
          fixTube
          fixBase

      compTube : [ φ ] → (i : Int) → X (p i , fcompTerm i O ∣ inl refl ∣)
      compTube u i =
        subst (curry X (p i))
          (symm (ixred _ (fcomp r p φ i O ∣ inl refl ∣) box ∣ inl u ∣))
          (boxrec (p i) (fcompArg i ∣ inl u ∣))

      compBase : _ [ φ ↦ compTube ◆ r ]
      compBase =
        ( subst (curry X (p r))
          (cong (fcompTerm r O) (trunc _ _))
          (fix .comp O (I≡IsCofProp O) .fst)
        , λ u →
          trans
            (cong (subst (curry X (p r)) (cong (fcompTerm r O) (trunc _ _)))
              (fix .comp O (I≡IsCofProp O) .snd u))
            (trans
              (substTrans (curry X (p r))
                (cong (fcompTerm r O) (trunc _ _))
                (symm (ixred _ (fcomp r p φ r O ∣ inr refl ∣) box ∣ inl u ∣)))
              (adjustSubstEq (curry X (p r))
                refl refl
                (symm (ixred _ (fcomp r p φ r O ∣ inl refl ∣) box ∣ inl u ∣))
                (trans
                  (cong (fcompTerm r O) (trunc ∣ inr refl ∣ ∣ inl refl ∣))
                  (symm (ixred _ (fcomp r p φ r O ∣ inr refl ∣) box ∣ inl u ∣)))
                refl))
        )

      compMain =
        χ r (λ i → p i , fcompTerm i O ∣ inl refl ∣)
          φ
          compTube
          compBase

      module _ (t : Int) where

        capTube : [ φ ∨ t ≈O ∨ t ≈I ] → (i : Int) → X (p r , fcompTerm r t ∣ inr refl ∣)
        capTube =
          ∨-rec φ (t ≈O ∨ t ≈I)
            (λ u _ → fixTube u t)
            (OI-rec t
              (λ {refl j →
                subst (curry X (p r))
                  (cong (fcompTerm r O) (trunc _ _))
                  (compMain .cap .fst .at j)})
              (λ {refl j → fixBase .fst}))
            (λ u → OI-elim t _
              (λ {refl → funext λ j →
                adjustSubstEq (curry X (p r))
                  (symm (ixred _ (fcomp r p φ r O ∣ inl refl ∣) box ∣ inl u ∣))
                  refl
                  (symm (ixred _ (fcomp r p φ r O ∣ inr refl ∣) box ∣ inl u ∣))
                  (cong (fcompTerm r O) (trunc _ _))
                  (compMain .cap .snd j u)})
              (λ {refl → funext λ j → fixBase .snd u}))

        capBase : _ [ φ ∨ t ≈O ∨ t ≈I ↦ capTube ◆ I ]
        capBase =
          ( fix .comp t (I≡IsCofProp t) .fst
          , ∨-elimEq φ (t ≈O ∨ t ≈I)
            (fix .comp t (I≡IsCofProp t) .snd)
            (∨-elimEq (t ≈O) (t ≈I)
              (λ {refl →
                adjustSubstEq (curry X (p r))
                  refl (cong (fcompTerm r O) (trunc _ _))
                  (cong (fcompTerm r O) (trunc _ _)) refl
                  (compMain .cap .fst .atI)})
              (λ {refl → symm (fix .cap (I≡IsCofProp I))}))
          )

        capMain =
          χ I (λ _ → p r , fcompTerm r t ∣ inr refl ∣)
            (φ ∨ t ≈O ∨ t ≈I)
            capTube
            capBase
            .comp O

      joined : (s t : Int) (w : ∥ t ≡ O ⊎ r ≡ s ∥)
        → X (p s , ixsup _ (fcomp r p φ s t w) box)
      joined s t =
        ∥⊎∥-elim uip uip _
          (λ {refl → compMain .comp s .fst})
          (λ {refl → capMain t .fst })
          (λ {refl refl →
            trans
              (capMain O .snd ∣ inr ∣ inl refl ∣ ∣)
              (trans
                (appCong
                  (subst-cong-assoc (curry X (p r))
                    (fcompTerm r O)
                    (trunc _ _)))
                (cong (subst (curry X (p r) ∘ fcompTerm r O) (trunc _ _))
                  (symm (compMain .cap .fst .atO))))})

      boundary : (s t : Int)
        (w : ∥ t ≡ O ⊎ r ≡ s ∥) (y : [ φ ∨ t ≈I ])
        → subst (curry X (p s))
            (ixred _ (fcomp r p φ s t w) box y)
            (joined s t w)
          ≡ boxrec (p s) (IxPoly.ev FRPoly (fcomp r p φ s t w) y)
      boundary s t =
        ∥⊎∥-elim uip uip _
          (λ {refl → ∥⊎∥-elim (cofIsProp φ) uip _
            (λ u →
              adjustSubstEq (curry X (p s))
                refl
                (symm (ixred _ (fcomp r p φ s O ∣ inl refl ∣) box ∣ inl u ∣))
                (ixred _ (fcomp r p φ s O ∣ inl refl ∣) box ∣ inl u ∣)
                refl
                (symm (compMain .comp s .snd u)))
            (λ O≡I → O≠I O≡I)
            (λ _ _ → uipImp)})
          (λ {refl → ∥⊎∥-elim (cofIsProp φ) uip _
            (λ u →
              adjustSubstEq (curry X (p s))
                refl
                (symm (ixred _ (fcomp r p φ r t ∣ inr refl ∣) box ∣ inl u ∣))
                (ixred _ (fcomp r p φ r t ∣ inr refl ∣) box ∣ inl u ∣)
                refl
                (symm (capMain t .snd ∣ inl u ∣)))
            (λ {refl →
              adjustSubstEq (curry X (p s))
                refl
                (symm (ixred _ (fcomp r p φ r I ∣ inr refl ∣) box ∣ inr refl ∣))
                (ixred _ (fcomp r p φ r I ∣ inr refl ∣) box ∣ inr refl ∣)
                refl
                (symm (capMain I .snd ∣ inr ∣ inr refl ∣ ∣))})
            (λ _ _ → uipImp)})
          (λ _ _ → funext λ y → uipImp)
