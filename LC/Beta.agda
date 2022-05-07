module LC.Beta where

open import LC.Term
open import Function using (flip; _∘_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open Star using (Star; ε; _◅_; _◅◅_) public
open import Relation.Binary.Core using (Rel)
open import Agda.Primitive using (lzero)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

infix 3 _→β_
data _→β_ {Γ} : Rel (Term Γ) lzero where
  β-red : ∀ {t1 t2} → app (abs t1) t2 →β t1 ⟦ t2 ⟧
  β-app₁ : ∀ {t2 t1 t1'} → t1 →β t1' → app t1 t2 →β app t1' t2
  β-app₂ : ∀ {t1 t2 t2'} → t2 →β t2' → app t1 t2 →β app t1 t2'
  β-abs : ∀ {t t'} → t →β t' → abs t →β abs t'

_→β*_ : ∀ {Γ} → Rel (Term Γ) lzero
_→β*_ = Star _→β_

β*-app₁ : ∀ {Γ} {t2 t1 t1' : Term Γ} → t1 →β* t1' → app t1 t2 →β* app t1' t2
β*-app₁ {t2 = t2} = Star.gmap (flip app t2) β-app₁

β*-app₂ : ∀ {Γ} {t1 t2 t2' : Term Γ} → t2 →β* t2' → app t1 t2 →β* app t1 t2'
β*-app₂ {t1 = t1} = Star.gmap (app t1) β-app₂

β*-app : ∀ {Γ} {t1 t1' : Term Γ} → t1 →β* t1' → ∀ {t2 t2'} → t2 →β* t2' → app t1 t2 →β* app t1' t2'
β*-app p1 p2 = β*-app₁ p1 ◅◅ β*-app₂ p2

β*-abs : ∀ {Γ} {t t' : Term (suc Γ)} → t →β* t' → abs t →β* abs t'
β*-abs = Star.gmap abs β-abs


infix 3 _→βP_
data _→βP_ {Γ} : Rel (Term Γ) lzero where
  βP-red : ∀ {t1 t1'} → t1 →βP t1' → ∀ {t2 t2'} → t2 →βP t2' → app (abs t1) t2 →βP t1' ⟦ t2' ⟧
  βP-var : ∀ i → var i →βP var i
  βP-app : ∀ {t1 t1'} → t1 →βP t1' → ∀ {t2 t2'} → t2 →βP t2' → app t1 t2 →βP app t1' t2'
  βP-abs : ∀ {t t'} → t →βP t' → abs t →βP abs t'

_→βP*_ : ∀ {Γ} → Rel (Term Γ) lzero
_→βP*_ = Star _→βP_

βP-reflexive : ∀ {Γ} {t : Term Γ} → t →βP t
βP-reflexive {t = var i} = βP-var i
βP-reflexive {t = app t t₁} = βP-app βP-reflexive βP-reflexive
βP-reflexive {t = abs t} = βP-abs βP-reflexive

βP-reduce* : ∀ {Γ} → Term Γ → Term Γ
βP-reduce* (var i) = var i
βP-reduce* (app t1@(var _) t2) = app (βP-reduce* t1) (βP-reduce* t2)
βP-reduce* (app t1@(app _ _) t2) = app (βP-reduce* t1) (βP-reduce* t2)
βP-reduce* (app (abs t1) t2) = βP-reduce* t1 ⟦ βP-reduce* t2 ⟧
βP-reduce* (abs t) = abs (βP-reduce* t)

βP-red* : ∀ {Γ} → (t : Term Γ) → t →βP βP-reduce* t
βP-red* (var i) = βP-var i
βP-red* (app t1@(var _) t2) = βP-app (βP-red* t1) (βP-red* t2)
βP-red* (app t1@(app _ _) t2) = βP-app (βP-red* t1) (βP-red* t2)
βP-red* (app (abs t1) t2) = βP-red (βP-red* t1) (βP-red* t2)
βP-red* (abs t) = βP-abs (βP-red* t)

→β⊂→βP : ∀ {Γ} → {t t' : Term Γ} → t →β t' → t →βP t'
→β⊂→βP β-red = βP-red βP-reflexive βP-reflexive
→β⊂→βP (β-app₁ p) = βP-app (→β⊂→βP p) βP-reflexive
→β⊂→βP (β-app₂ p) = βP-app βP-reflexive (→β⊂→βP p)
→β⊂→βP (β-abs p) = βP-abs (→β⊂→βP p)

→β*⊂→βP* : ∀ {Γ} → {t t' : Term Γ} → t →β* t' → Star _→βP_ t t'
→β*⊂→βP* = Star.map →β⊂→βP

→βP⊂→β* : ∀ {Γ} → {t t' : Term Γ} → t →βP t' → t →β* t'
→βP⊂→β* (βP-red p₁ p₂) = β*-app (β*-abs (→βP⊂→β* p₁)) (→βP⊂→β* p₂) ◅◅ β-red ◅ ε
→βP⊂→β* (βP-var i) = ε
→βP⊂→β* (βP-app p₁ p₂) = β*-app (→βP⊂→β* p₁) (→βP⊂→β* p₂)
→βP⊂→β* (βP-abs p) = β*-abs (→βP⊂→β* p)

→βP*⊂→β* : ∀ {Γ} → {t t' : Term Γ} → t →βP* t' → t →β* t'
→βP*⊂→β* = Star.concat ∘ Star.map →βP⊂→β*


rename-β : ∀ {Γ Δ} → (ρ : Γ ⊆ Δ) → (∀ {t t' : Term Γ} → t →β t' → rename ρ t →β rename ρ t')
rename-β ρ (β-red {t1 = t1} {t2 = t2}) rewrite distrib-rename-⟦⟧ ρ t1 t2 = β-red
rename-β ρ (β-app₁ p) = β-app₁ (rename-β ρ p)
rename-β ρ (β-app₂ p) = β-app₂ (rename-β ρ p)
rename-β ρ (β-abs p) = β-abs (rename-β (lift ρ) p)

rename-βP : ∀ {Γ Δ} → (ρ : Γ ⊆ Δ) → (∀ {t t' : Term Γ} → t →βP t' → rename ρ t →βP rename ρ t')
rename-βP ρ (βP-red {t1' = t1'} p {t2' = t2'} p₁) rewrite distrib-rename-⟦⟧ ρ t1' t2' = βP-red (rename-βP (lift ρ) p) (rename-βP ρ p₁)
rename-βP ρ (βP-var i) = βP-var (ρ i)
rename-βP ρ (βP-app p p₁) = βP-app (rename-βP ρ p) (rename-βP ρ p₁)
rename-βP ρ (βP-abs p) = βP-abs (rename-βP (lift ρ) p)

subst-βP : ∀ {Γ Δ} {σ σ' : Γ ◁ Δ} → (∀ (i : Fin Γ) → σ i →βP σ' i) → (∀ {t t' : Term Γ} → t →βP t' → subst σ t →βP subst σ' t')
subst-βP {σ' = σ'} ps (βP-red {t1' = t1'} p {t2' = t2'} p₁) rewrite distrib-subst-⟦⟧ σ' t1' t2' = βP-red (subst-βP (λ { here → βP-var here ; (there i) → rename-βP there (ps i) }) p) (subst-βP ps p₁)
subst-βP ps (βP-var i) = ps i
subst-βP ps (βP-app p p₁) = βP-app (subst-βP ps p) (subst-βP ps p₁)
subst-βP ps (βP-abs p) = βP-abs (subst-βP (λ { here → βP-var here ; (there i) → rename-βP there (ps i) }) p)

⟦⟧-βP : ∀ {Γ} {t1 t1' : Term (suc Γ)} → t1 →βP t1' → ∀ {t2 t2'} → t2 →βP t2' → t1 ⟦ t2 ⟧ →βP t1' ⟦ t2' ⟧
⟦⟧-βP p1 p2 = subst-βP (λ { here → p2 ; (there i) → βP-var i }) p1


inv-rename-β : ∀ {Γ Δ} (ρ : Γ ⊆ Δ) (t1 : Term Γ) (t2' : Term Δ) → rename ρ t1 →β t2' → ∃ (λ t2 → t2' ≡ rename ρ t2 × t1 →β t2)
inv-rename-β ρ (var i) t2' ()
inv-rename-β ρ (app s1@(var _) t1) _ (β-app₁ ())
inv-rename-β ρ (app s1@(var _) t1) (app .(rename ρ s1) t2') (β-app₂ p) = let t2 , eq , q = inv-rename-β ρ t1 t2' p in app s1 t2 , cong (app (rename ρ s1)) eq , β-app₂ q
inv-rename-β ρ (app s1@(app _ _) t1) (app s2' .(rename ρ t1)) (β-app₁ p) = let s2 , eq , q = inv-rename-β ρ s1 s2' p in app s2 t1 , cong (flip app (rename ρ t1)) eq , β-app₁ q
inv-rename-β ρ (app s1@(app _ _) t1) (app .(rename ρ s1) t2') (β-app₂ p) = let t2 , eq , q = inv-rename-β ρ t1 t2' p in app s1 t2 , cong (app (rename ρ s1)) eq , β-app₂ q
inv-rename-β ρ (app (abs s1) t1) .(rename (lift ρ) s1 ⟦ rename ρ t1 ⟧) β-red rewrite sym (distrib-rename-⟦⟧ ρ s1 t1) = s1 ⟦ t1 ⟧ , refl , β-red
inv-rename-β ρ (app s1@(abs _) t1) (app s2' .(rename ρ t1)) (β-app₁ p) = let s2 , eq , q = inv-rename-β ρ s1 s2' p in app s2 t1 , cong (flip app (rename ρ t1)) eq , β-app₁ q
inv-rename-β ρ (app s1@(abs _) t1) (app .(rename ρ s1) t2') (β-app₂ p) = let t2 , eq , q = inv-rename-β ρ t1 t2' p in app s1 t2 , cong (app (rename ρ s1)) eq , β-app₂ q
inv-rename-β ρ (abs t1) (abs t2') (β-abs p) = let t2 , eq , q = inv-rename-β (lift ρ) t1 t2' p in abs t2 , cong abs eq , β-abs q
