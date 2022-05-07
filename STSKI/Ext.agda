{-# OPTIONS --with-K #-}

module STSKI.Ext (T : Set) where

open import STLC.Type T
open import STSKI.Term T
open import STSKI.STLC T
import STLC.Term T as Lam
open import STLC.Combinators T
open import STLC.Beta T
open import Function using (flip; _∘_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open import Relation.Binary.Core using (Rel)
open import Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; inspect; [_])


data _→Ext_ {Γ} : ∀ {a} → Rel (Γ ⊢ a) lzero where
  I-red : ∀ {a} A → app (I {Γ} {a}) A →Ext A
  K-red : ∀ {a b} A B → app (app (K {Γ} {a} {b}) A) B →Ext A
  S-red : ∀ {a b c} A B C → app (app (app (S {Γ} {a} {b} {c}) A) B) C →Ext app (app A C) (app B C)
  I-ext : ∀ {a} → I {Γ} {a} →Ext abs (app I (var here))
  K-ext : ∀ {a b} → K {Γ} {a} {b} →Ext abs (abs (app (app K (var (there here))) (var here)))
  S-ext : ∀ {a b c} → S {Γ} {a} {b} {c} →Ext abs (abs (abs (app (app (app S (var (there (there here)))) (var (there here))) (var here))))
  Ext-app₁ : ∀ {a b t2} {t1 t1' : Γ ⊢ a ⇒ b} → t1 →Ext t1' → app t1 t2 →Ext app t1' t2
  Ext-app₂ : ∀ {a b} {t1 : Γ ⊢ a ⇒ b} {t2 t2'} → t2 →Ext t2' → app t1 t2 →Ext app t1 t2'
  w-ext : ∀ {a b} {A A' : a ∷ Γ ⊢ b} → A →Ext A' → abs A →Ext abs A'
  
_→Ext*_ : ∀ {Γ a} → Rel (Γ ⊢ a) lzero
_→Ext*_ = Star _→Ext_

Ext*-reflexive : ∀ {Γ a} {t t' : Γ ⊢ a} → t ≡ t' → t →Ext* t'
Ext*-reflexive refl = ε

Ext*-app₁ : ∀ {Γ a b t2} {t1 t1' : Γ ⊢ a ⇒ b} → t1 →Ext* t1' → app t1 t2 →Ext* app t1' t2
Ext*-app₁ {t2 = t2} = Star.gmap (flip app t2) Ext-app₁

Ext*-app₂ : ∀ {Γ a b} {t1 : Γ ⊢ a ⇒ b} {t2 t2'} → t2 →Ext* t2' → app t1 t2 →Ext* app t1 t2'
Ext*-app₂ {t1 = t1} = Star.gmap (app t1) Ext-app₂

Ext*-app : ∀ {Γ a b} {t1 t1' : Γ ⊢ a ⇒ b} → t1 →Ext* t1' → ∀ {t2 t2'} → t2 →Ext* t2' → app t1 t2 →Ext* app t1' t2'
Ext*-app p1 p2 = Ext*-app₁ p1 ◅◅ Ext*-app₂ p2

w-ext* : ∀ {Γ a b} {A A' : a ∷ Γ ⊢ b} → A →Ext* A' → abs A →Ext* abs A'
w-ext* = Star.gmap abs w-ext

id-ski-lam : ∀ {Γ a} (A : Γ ⊢ a) → A →Ext* ski-map (lam-map A)
id-ski-lam I = I-ext ◅ w-ext (I-red (var here)) ◅ ε 
id-ski-lam K = K-ext ◅ w-ext (w-ext (K-red (var (there here)) (var here))) ◅ ε
id-ski-lam S = S-ext ◅ w-ext (w-ext (w-ext (S-red (var (there (there here))) (var (there here)) (var here)))) ◅ ε
id-ski-lam (var i) = ε
id-ski-lam (app A B) = Ext*-app (id-ski-lam A) (id-ski-lam B)

Ext*-β-red : ∀ {Γ a b} (A : a ∷ Γ ⊢ b) B → app (abs A) B →Ext* (A ⟦ B ⟧)
Ext*-β-red I B = K-red I B ◅ ε
Ext*-β-red K B = K-red K B ◅ ε
Ext*-β-red S B = K-red S B ◅ ε
Ext*-β-red (var here) B = I-red B ◅ ε
Ext*-β-red (var (there i)) B = K-red (var i) B ◅ ε
Ext*-β-red (app A1 A2) B with abs' A1 | inspect abs' A1
... | Abs-I | [ eq1 ] = S-red I (abs A2) B ◅ Ext*-app (I-red B ◅ Ext*-reflexive {!!}) (Ext*-β-red A2 B)
... | Abs-S _ _ | [ eq1 ] rewrite cong abs-to-term (sym eq1)= S-red (abs A1) (abs A2) B ◅ Ext*-app (Ext*-β-red A1 B) (Ext*-β-red A2 B)
... | Abs-K A1' | [ eq1 ] with abs' A2 | inspect abs' A2
-- ... | Abs-I | _ rewrite cong abs-to-term (sym eq1) = S-red (abs A1) I B ◅ Ext*-app (Ext*-β-red A1 B) (I-red B ◅ ε)
... | Abs-S _ _ | [ eq2 ] rewrite cong abs-to-term (sym eq1) | cong abs-to-term (sym eq2) = S-red (abs A1) (abs A2) B ◅ Ext*-app (Ext*-β-red A1 B) (Ext*-β-red A2 B)
-- ... | Abs-K A2' | _ rewrite eqA1 | eqA2 = K-red (app A1' A2') B ◅ Ext*-reflexive (cong₂ app (⟦⟧-weak B A1') (⟦⟧-weak B A2'))

β⇒Ext* : ∀ {Γ a} {t t' : Γ Lam.⊢ a} → t →β t' → ski-map t →Ext* ski-map t'
β⇒Ext* (β-red {_} {_} {s} {t}) rewrite distrib-ski-⟦⟧ s t = Ext*-β-red (ski-map s) (ski-map t)
β⇒Ext* (β-app₁ p) = Ext*-app₁ (β⇒Ext* p)
β⇒Ext* (β-app₂ p) = Ext*-app₂ (β⇒Ext* p)
β⇒Ext* (β-abs p) = w-ext* (β⇒Ext* p)

Ext⇒β≈ : ∀ {Γ a} {A A' : Γ ⊢ a} → A →Ext A' → lam-map A β≈ lam-map A'
Ext⇒β≈ (I-red A) = →β*⊂β≈ 𝒊-red
Ext⇒β≈ (K-red A B) = →β*⊂β≈ 𝒌-red
Ext⇒β≈ (S-red A B C) = →β*⊂β≈ 𝒔-red
Ext⇒β≈ I-ext = β≈-sym (→β*⊂β≈ I-ext-lemma)
Ext⇒β≈ K-ext = β≈-sym (→β*⊂β≈ K-ext-lemma)
Ext⇒β≈ S-ext = β≈-sym (→β*⊂β≈ S-ext-lemma)
Ext⇒β≈ (Ext-app₁ p) = β≈-app₁ (Ext⇒β≈ p)
Ext⇒β≈ (Ext-app₂ p) = β≈-app₂ (Ext⇒β≈ p)
Ext⇒β≈ (w-ext {A = A} {A' = A'} p) = β≈-trans (→β*⊂β≈ (comm-lam-abs A)) (β≈-trans (β≈-abs (Ext⇒β≈ p)) (β≈-sym (→β*⊂β≈ (comm-lam-abs A')))) 
