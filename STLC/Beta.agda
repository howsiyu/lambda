module STLC.Beta (T : Set) where

open import STLC.Type T
open import STLC.Term T
open import Function using (flip; _∘_)
open import Data.Star using (Star; ε; _◅_; _◅◅_; gmap; concat)
import Data.Star using (map)
open import Relation.Binary.Core using (Rel)
open import Agda.Primitive using (lzero)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

infix 3 _→β_
data _→β_ {Γ} : ∀ {a} → Rel (Γ ⊢ a) lzero where
  β-red : ∀ {a b} {t1 : (a ∷ Γ) ⊢ b} {t2} → app (abs t1) t2 →β t1 ⟦ t2 ⟧
  β-app₁ : ∀ {a b t2} {t1 t1' : Γ ⊢ (a ⇒ b)} → t1 →β t1' → app t1 t2 →β app t1' t2
  β-app₂ : ∀ {a b} {t1 : Γ ⊢ (a ⇒ b)} {t2 t2'} → t2 →β t2' → app t1 t2 →β app t1 t2'
  β-abs : ∀ {a b} {t t' : (a ∷ Γ) ⊢ b} → t →β t' → abs t →β abs t'

_β←_ : ∀ {Γ a} → Rel (Γ ⊢ a) lzero
_β←_ = flip _→β_

_→β*_ : ∀ {Γ a} → Rel (Γ ⊢ a) lzero
_→β*_ = Star _→β_

_*β←_ : ∀ {Γ a} → Rel (Γ ⊢ a) lzero
_*β←_ = flip _→β*_

β*-reflexive : ∀ {Γ a} {t t' : Γ ⊢ a} → t ≡ t' → t →β* t'
β*-reflexive refl = ε

β*-app₁ : ∀ {Γ a b t2} {t1 t1' : Γ ⊢ a ⇒ b} → t1 →β* t1' → app t1 t2 →β* app t1' t2
β*-app₁ {t2 = t2} = gmap (flip app t2) β-app₁

β*-app₂ : ∀ {Γ a b} {t1 : Γ ⊢ a ⇒ b} {t2 t2'} → t2 →β* t2' → app t1 t2 →β* app t1 t2'
β*-app₂ {t1 = t1} = gmap (app t1) β-app₂

β*-app : ∀ {Γ a b} {t1 t1' : Γ ⊢ a ⇒ b} → t1 →β* t1' → ∀ {t2 t2'} → t2 →β* t2' → app t1 t2 →β* app t1' t2'
β*-app p1 p2 = β*-app₁ p1 ◅◅ β*-app₂ p2

β*-abs : ∀ {Γ a b} {t t' : (a ∷ Γ) ⊢ b} → t →β* t' → abs t →β* abs t'
β*-abs = gmap abs β-abs

infix 3 _→βP_
data _→βP_ {Γ} : ∀ {a} → Rel (Γ ⊢ a) lzero where
  βP-red : ∀ {a b} {t1 t1' : a ∷ Γ ⊢ b} → t1 →βP t1' → ∀ {t2 t2'} → t2 →βP t2' → app (abs t1) t2 →βP t1' ⟦ t2' ⟧
  βP-var : ∀ {a} → (i : Γ ∋ a) → var i →βP var i
  βP-app : ∀ {a b} {t1 t1' : Γ ⊢ a ⇒ b} → t1 →βP t1' → ∀ {t2 t2'} → t2 →βP t2' → app t1 t2 →βP app t1' t2'
  βP-abs : ∀ {a b} {t t' : a ∷ Γ ⊢ b} → t →βP t' → abs t →βP abs t'

_→βP*_ : ∀ {Γ a} → Rel (Γ ⊢ a) lzero
_→βP*_ = Star _→βP_

βP-refl : ∀ {Γ a} {t : Γ ⊢ a} → t →βP t
βP-refl {t = var i} = βP-var i
βP-refl {t = app t t₁} = βP-app βP-refl βP-refl
βP-refl {t = abs t} = βP-abs βP-refl

βP-app₁ : ∀ {Γ a b t2} {t1 t1' : Γ ⊢ a ⇒ b} → t1 →βP t1' → app t1 t2 →βP app t1' t2
βP-app₁ p = βP-app p βP-refl

βP-app₂ : ∀ {Γ a b} {t1 : Γ ⊢ a ⇒ b} {t2 t2'} → t2 →βP t2' → app t1 t2 →βP app t1 t2'
βP-app₂ p = βP-app βP-refl p

βP*-app₁ : ∀ {Γ a b t2} {t1 t1' : Γ ⊢ a ⇒ b} → t1 →βP* t1' → app t1 t2 →βP* app t1' t2
βP*-app₁ {t2 = t2} = gmap (flip app t2) βP-app₁

βP*-app₂ : ∀ {Γ a b} {t1 : Γ ⊢ a ⇒ b} {t2 t2'} → t2 →βP* t2' → app t1 t2 →βP* app t1 t2'
βP*-app₂ {t1 = t1} = gmap (app t1) βP-app₂

βP*-app : ∀ {Γ a b} {t1 t1' : Γ ⊢ a ⇒ b} → t1 →βP* t1' → ∀ {t2 t2'} → t2 →βP* t2' → app t1 t2 →βP* app t1' t2'
βP*-app p1 p2 = βP*-app₁ p1 ◅◅ βP*-app₂ p2

βP*-abs : ∀ {Γ a b} {t t' : (a ∷ Γ) ⊢ b} → t →βP* t' → abs t →βP* abs t'
βP*-abs = gmap abs βP-abs

βP-reduce* : ∀ {Γ a} → Γ ⊢ a → Γ ⊢ a
βP-reduce* (var i) = var i
βP-reduce* (app t1@(var _) t2) = app (βP-reduce* t1) (βP-reduce* t2)
βP-reduce* (app t1@(app _ _) t2) = app (βP-reduce* t1) (βP-reduce* t2)
βP-reduce* (app (abs t1) t2) = βP-reduce* t1 ⟦ βP-reduce* t2 ⟧
βP-reduce* (abs t) = abs (βP-reduce* t)

βP-red* : ∀ {Γ a} → (t : Γ ⊢ a) → t →βP βP-reduce* t
βP-red* (var i) = βP-var i
βP-red* (app t1@(var _) t2) = βP-app (βP-red* t1) (βP-red* t2)
βP-red* (app t1@(app _ _) t2) = βP-app (βP-red* t1) (βP-red* t2)
βP-red* (app (abs t1) t2) = βP-red (βP-red* t1) (βP-red* t2)
βP-red* (abs t) = βP-abs (βP-red* t)

→β⊂→βP : ∀ {Γ a} → {t t' : Γ ⊢ a} → t →β t' → t →βP t'
→β⊂→βP β-red = βP-red βP-refl βP-refl
→β⊂→βP (β-app₁ p) = βP-app (→β⊂→βP p) βP-refl
→β⊂→βP (β-app₂ p) = βP-app βP-refl (→β⊂→βP p)
→β⊂→βP (β-abs p) = βP-abs (→β⊂→βP p)

→β*⊂→βP* : ∀ {Γ a} → {t t' : Γ ⊢ a} → t →β* t' → Star _→βP_ t t'
→β*⊂→βP* = Data.Star.map →β⊂→βP

→βP⊂→β* : ∀ {Γ a} → {t t' : Γ ⊢ a} → t →βP t' → t →β* t'
→βP⊂→β* (βP-red p₁ p₂) = β*-app (β*-abs (→βP⊂→β* p₁)) (→βP⊂→β* p₂) ◅◅ β-red ◅ ε
→βP⊂→β* (βP-var i) = ε
→βP⊂→β* (βP-app p₁ p₂) = β*-app (→βP⊂→β* p₁) (→βP⊂→β* p₂)
→βP⊂→β* (βP-abs p) = β*-abs (→βP⊂→β* p)

→βP*⊂→β* : ∀ {Γ a} → {t t' : Γ ⊢ a} → t →βP* t' → t →β* t'
→βP*⊂→β* = concat ∘ Data.Star.map →βP⊂→β*


map-β : ∀ {Γ Δ} → (ρ : Γ ⊆ Δ) → (∀ {a} {t t' : Γ ⊢ a} → t →β t' → map ρ t →β map ρ t')
map-β ρ (β-red {t1 = t1} {t2 = t2}) rewrite distrib-map-⟦⟧ ρ t1 t2 = β-red
map-β ρ (β-app₁ p) = β-app₁ (map-β ρ p)
map-β ρ (β-app₂ p) = β-app₂ (map-β ρ p)
map-β ρ (β-abs p) = β-abs (map-β (lift ρ) p)

map-βP : ∀ {Γ Δ} → (ρ : Γ ⊆ Δ) → (∀ {a} {t t' : Γ ⊢ a} → t →βP t' → map ρ t →βP map ρ t')
map-βP ρ (βP-red {t1' = t1'} p {t2' = t2'} p₁) rewrite distrib-map-⟦⟧ ρ t1' t2' = βP-red (map-βP (lift ρ) p) (map-βP ρ p₁)
map-βP ρ (βP-var i) = βP-var (ρ i)
map-βP ρ (βP-app p p₁) = βP-app (map-βP ρ p) (map-βP ρ p₁)
map-βP ρ (βP-abs p) = βP-abs (map-βP (lift ρ) p)

bind-βP : ∀ {Γ Δ} {σ σ' : Γ ◁ Δ} → (∀ {a} (i : Γ ∋ a) → σ i →βP σ' i) → (∀ {a} {t t' : Γ ⊢ a} → t →βP t' → bind σ t →βP bind σ' t')
bind-βP {σ' = σ'} ps (βP-red {t1' = t1'} p {t2' = t2'} p₁) rewrite distrib-bind-⟦⟧ σ' t1' t2' = βP-red (bind-βP (λ { here → βP-var here ; (there i) → map-βP there (ps i) }) p) (bind-βP ps p₁)
bind-βP ps (βP-var i) = ps i
bind-βP ps (βP-app p p₁) = βP-app (bind-βP ps p) (bind-βP ps p₁)
bind-βP ps (βP-abs p) = βP-abs (bind-βP (λ { here → βP-var here ; (there i) → map-βP there (ps i) }) p)

⟦⟧-βP : ∀ {Γ a b} {t1 t1' : (a ∷ Γ) ⊢ b} → t1 →βP t1' → ∀ {t2 t2'} → t2 →βP t2' → t1 ⟦ t2 ⟧ →βP t1' ⟦ t2' ⟧
⟦⟧-βP p1 p2 = bind-βP (λ { here → p2 ; (there i) → βP-var i }) p1


inv-map-β : ∀ {Γ Δ a} (ρ : Γ ⊆ Δ) (t1 : Γ ⊢ a) (t2' : Δ ⊢ a) → map ρ t1 →β t2' → ∃ (λ t2 → t2' ≡ map ρ t2 × t1 →β t2)
inv-map-β ρ (var i) t2' ()
inv-map-β ρ (app s1@(var _) t1) _ (β-app₁ ())
inv-map-β ρ (app s1@(var _) t1) (app .(map ρ s1) t2') (β-app₂ p) = let t2 , eq , q = inv-map-β ρ t1 t2' p in app s1 t2 , cong (app (map ρ s1)) eq , β-app₂ q
inv-map-β ρ (app s1@(app _ _) t1) (app s2' .(map ρ t1)) (β-app₁ p) = let s2 , eq , q = inv-map-β ρ s1 s2' p in app s2 t1 , cong (flip app (map ρ t1)) eq , β-app₁ q
inv-map-β ρ (app s1@(app _ _) t1) (app .(map ρ s1) t2') (β-app₂ p) = let t2 , eq , q = inv-map-β ρ t1 t2' p in app s1 t2 , cong (app (map ρ s1)) eq , β-app₂ q
inv-map-β ρ (app (abs s1) t1) .(map (lift ρ) s1 ⟦ map ρ t1 ⟧) β-red rewrite sym (distrib-map-⟦⟧ ρ s1 t1) = s1 ⟦ t1 ⟧ , refl , β-red
inv-map-β ρ (app s1@(abs _) t1) (app s2' .(map ρ t1)) (β-app₁ p) = let s2 , eq , q = inv-map-β ρ s1 s2' p in app s2 t1 , cong (flip app (map ρ t1)) eq , β-app₁ q
inv-map-β ρ (app s1@(abs _) t1) (app .(map ρ s1) t2') (β-app₂ p) = let t2 , eq , q = inv-map-β ρ t1 t2' p in app s1 t2 , cong (app (map ρ s1)) eq , β-app₂ q
inv-map-β ρ (abs t1) (abs t2') (β-abs p) = let t2 , eq , q = inv-map-β (lift ρ) t1 t2' p in abs t2 , cong abs eq , β-abs q


infix 3 _β≈_
data _β≈_ {Γ} : ∀ {a} → Rel (Γ ⊢ a) lzero where
  β≈-refl : ∀ {a} {t : Γ ⊢ a} → t β≈ t
  β≈-sym : ∀ {a} {t t' : Γ ⊢ a} → t β≈ t' → t' β≈ t
  β≈-trans : ∀ {a} {t t' t'' : Γ ⊢ a} → t β≈ t' → t' β≈ t'' → t β≈ t''
  β≈-red : ∀ {a b} {t1 : a ∷ Γ ⊢ b} {t2} → app (abs t1) t2 β≈ t1 ⟦ t2 ⟧
  β≈-app : ∀ {a b} {t1 t1' : Γ ⊢ a ⇒ b} → t1 β≈ t1' → ∀ {t2 t2'} → t2 β≈ t2' → app t1 t2 β≈ app t1' t2'
  β≈-abs : ∀ {a b} {t t' : a ∷ Γ ⊢ b} → t β≈ t' → abs t β≈ abs t'

β≈-app₁ : ∀ {Γ a b t2} {t1 t1' : Γ ⊢ a ⇒ b} → t1 β≈ t1' → app t1 t2 β≈ app t1' t2
β≈-app₁ p = β≈-app p β≈-refl

β≈-app₂ : ∀ {Γ a b} {t1 : Γ ⊢ a ⇒ b} {t2 t2'} → t2 β≈ t2' → app t1 t2 β≈ app t1 t2'
β≈-app₂ p = β≈-app β≈-refl p

→β⊂β≈ : ∀ {Γ a} {t t' : Γ ⊢ a} → t →β t' → t β≈ t'
→β⊂β≈ β-red = β≈-red
→β⊂β≈ (β-app₁ p) = β≈-app₁ (→β⊂β≈ p)
→β⊂β≈ (β-app₂ p) = β≈-app₂ (→β⊂β≈ p)
→β⊂β≈ (β-abs p) = β≈-abs (→β⊂β≈ p)

→β*⊂β≈ : ∀ {Γ a} {t t' : Γ ⊢ a} → t →β* t' → t β≈ t'
→β*⊂β≈ ε = β≈-refl
→β*⊂β≈ (p ◅ ps) = β≈-trans (→β⊂β≈ p) (→β*⊂β≈ ps)
