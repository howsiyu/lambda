module STLC.WeakNormalization (T : Set) where

open import STLC.Type T
open import STLC.Term T
open import STLC.Beta T
open import Function using (_on_; _∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; inspect; [_])
open import Induction.WellFounded
open import Data.Nat.Induction using (<-wellFounded)
open import Agda.Primitive using (lzero)
open import Relation.Unary using (_⊆′_)

data redex {Γ : Ctx} : ∀ {a} → Γ ⊢ a → Set where
  r-red : ∀ {a b} {s : a ∷ Γ ⊢ b} {t : Γ ⊢ a} → redex (app (abs s) t)
  r-app₁ : ∀ {a b} {s : Γ ⊢ a ⇒ b} {t} → redex s → redex (app s t)
  r-app₂ : ∀ {a b} {s : Γ ⊢ a ⇒ b} {t} → redex t → redex (app s t)
  r-abs : ∀ {a b} {t : a ∷ Γ ⊢ b} → redex t → redex (abs t)

data Degree : Set where
  _⇛_ : Type → Type → Degree

deg : ∀ {Γ a} {t : Γ ⊢ a} → redex t → Degree
deg (r-red {a} {b}) = a ⇛ b
deg (r-app₁ r) = deg r
deg (r-app₂ r) = deg r
deg (r-abs r) = deg r

map-deg : ∀ {Γ Δ} (ρ : Γ ⊆ Δ) → ∀ {a} (t : Γ ⊢ a) → (r : redex (map ρ t)) → ∃ (λ (r' : redex t) → deg r ≡ deg r')
map-deg ρ (var i) ()
map-deg ρ (app (var i) t) (r-app₁ ())
map-deg ρ (app s t) (r-app₁ r) = let (r' , eq) = map-deg ρ s r in r-app₁ r' , eq
map-deg ρ (app s t) (r-app₂ r) = let (r' , eq) = map-deg ρ t r in r-app₂ r' , eq
map-deg ρ (app (abs s) t) r-red = r-red , refl
map-deg ρ (abs t) (r-abs r) = let (r' , eq) = map-deg (lift ρ) t r in r-abs r' , eq

data Isabs : ∀ {Γ} a → Degree → Γ ⊢ a → Set where
  isabs : ∀ {Γ} a b t → Isabs {Γ} (a ⇒ b) (a ⇛ b) (abs t)

bind-deg : ∀ {Γ Δ} (σ : Γ ◁ Δ) → ∀ {b} (t : Γ ⊢ b) → (r : redex (bind σ t)) → ∃ (λ (r' : redex t) → deg r ≡ deg r') ⊎ ∃ (λ a → ∃ (λ (i : Γ ∋ a) → Isabs a (deg r) (σ i) ⊎ ∃ (λ (r' : redex (σ i)) → deg r ≡ deg r')))
bind-deg σ (var i) r = inj₂ (_ , i , inj₂ (r , refl))
bind-deg σ (app s t) r with bind σ s | inspect (bind σ) s
bind-deg σ (app s t) (r-app₁ ()) | var _ | _
bind-deg σ (app s t) (r-app₂ r) | _ | _ with bind-deg σ t r
... | inj₁ (r' , eq) = inj₁ (r-app₂ r' , eq)
... | inj₂ p = inj₂ p
bind-deg σ (app s t) (r-app₁ r) | _ | [ eq ] rewrite sym eq with bind-deg σ s r
... | inj₁ (r' , eq2) = inj₁ (r-app₁ r' , eq2)
... | inj₂ p = inj₂ p
bind-deg σ (app (var i) t) r-red | abs {a} {b} s' | [ eq ] = inj₂ (_ , i , inj₁ goal)
  where
  goal : Isabs (a ⇒ b) (a ⇛ b) (σ i)
  goal rewrite eq = isabs a b s'
bind-deg σ (app (app _ _) t) r-red | abs s' | [ () ]
bind-deg σ (app (abs s) t) r-red | abs s' | [ eq ] = inj₁ (r-red , refl)
bind-deg σ (abs t) (r-abs r) with bind-deg (Mlift σ) t r
bind-deg σ (abs t) (r-abs r) | inj₁ (r' , eq) = inj₁ (r-abs r' , eq)
bind-deg σ (abs t) (r-abs r) | inj₂ (_ , here , inj₁ ())
bind-deg σ (abs t) (r-abs r) | inj₂ (_ , here , inj₂ ())
bind-deg σ (abs t) (r-abs r) | inj₂ (a , there i , inj₁ eqs) with σ i | inspect σ i | deg r
bind-deg σ (abs t) (r-abs r) | inj₂ (a , there i , inj₁ ()) | var _ | _ | _
bind-deg σ (abs t) (r-abs r) | inj₂ (a , there i , inj₁ ()) | app _ _ | _ | _
bind-deg σ (abs t) (r-abs r) | inj₂ (.(a ⇒ b) , there i , inj₁ (isabs a b _)) | abs t' | [ eq ] | .(a ⇛ b) = inj₂ (a ⇒ b , i , inj₁ goal)
  where
  goal : Isabs (a ⇒ b) (a ⇛ b) (σ i)
  goal rewrite eq = isabs a b t'
bind-deg σ (abs t) (r-abs r) | inj₂ (a , there i , inj₂ (r' , eq)) = let (r'' , eq') = map-deg there (σ i) r' in inj₂ (a , i , inj₂ (r'' , trans eq eq'))

⟦⟧-deg : ∀ {Γ a b} (s : a ∷ Γ ⊢ b) t → (r : redex (s ⟦ t ⟧)) → ∃ (λ (r' : redex s) → deg r ≡ deg r') ⊎ Isabs a (deg r) t ⊎ ∃ (λ (r' : redex t) → deg r ≡ deg r')
⟦⟧-deg s t r with bind-deg (Msub t) s r
⟦⟧-deg s t r | inj₁ p = inj₁ p
⟦⟧-deg s t r | inj₂ (a , here , inj₁ eqs) = inj₂ (inj₁ eqs)
⟦⟧-deg s t r | inj₂ (a , there i , inj₁ ())
⟦⟧-deg s t r | inj₂ (a , here , inj₂ req) = inj₂ (inj₂ req)
⟦⟧-deg s t r | inj₂ (a , there i , inj₂ (() , eq))


infix 9 _≺ₜ_
data _≺ₜ_ (a : Type) : Type → Set where
  left : ∀ {b} → a ≺ₜ (a ⇒ b)
  right : ∀ {b} → a ≺ₜ (b ⇒ a)

deg-to-type : Degree → Type
deg-to-type (a ⇛ b) = a ⇒ b

infix 9 _≺_
_≺_ : Rel Degree lzero
_≺_ = _≺ₜ_ on deg-to-type

star-deg : ∀ {Γ a} (t : Γ ⊢ a) (r : redex (βP-reduce* t)) → ∃ (λ (r2 : redex t) → deg r ≺ deg r2)
star-deg (var _) ()
star-deg (app (var _) t) (r-app₁ ())
star-deg (app (var _) t) (r-app₂ r) = let r2 , le = star-deg t r in r-app₂ r2 , le
star-deg (app s@(app _ _) t) r with βP-reduce* s | inspect βP-reduce* s
star-deg (app (app _ _) t) (r-app₂ r) | _ | [ eq ] = let r2 , le = star-deg t r in r-app₂ r2 , le
star-deg (app s@(app _ _) t) (r-app₁ r) | _ | [ eq ] rewrite sym eq = let r2 , le = star-deg s r in r-app₁ r2 , le
star-deg (app (app (var _) _) t) r | abs s' | [ () ]
star-deg (app (app (app _ _) _) t) r | abs s' | [ () ]
star-deg (app (app (abs s1) s2) t) r-red | abs s' | [ eq ] = r-app₁ r-red , right
star-deg (app (abs s) t) r with ⟦⟧-deg (βP-reduce* s) (βP-reduce* t) r
star-deg (app (abs s) t) r | inj₁ (r' , eq) rewrite eq = let r2 , le = star-deg s r' in r-app₁ (r-abs r2) , le
star-deg (app (abs s) t) r | inj₂ (inj₁ eqs) with βP-reduce* t | deg r
star-deg (app (abs s) t) r | inj₂ (inj₁ ()) | var _ | _
star-deg (app (abs s) t) r | inj₂ (inj₁ ()) | app _ _ | _
star-deg (app (abs s) t) r | inj₂ (inj₁ (isabs a b t')) | abs .t' | .(a ⇛ b) = r-red , left
star-deg (app (abs s) t) r | inj₂ (inj₂ (r' , eq)) rewrite eq = let r2 , le = star-deg t r' in r-app₂ r2 , le
star-deg (abs t) (r-abs r) = let r2 , le = star-deg t r in r-abs r2 , le

normal : ∀ {Γ a} → Γ ⊢ a → Set
normal t = ¬ (redex t)

redex? : ∀ {Γ a} → (t : Γ ⊢ a) → Dec (redex t)
redex? (var i) = no (λ ())
redex? (app (var i) t) with redex? t
... | yes r = yes (r-app₂ r)
... | no ctr = no (λ { (r-app₁ ()) ; (r-app₂ r) → ctr r })
redex? (app s@(app _ _) t) with redex? s
... | yes r = yes (r-app₁ r)
... | no ctr1 with redex? t
... | yes r = yes (r-app₂ r)
... | no ctr2 = no (λ { (r-app₁ r) → ctr1 r ; (r-app₂ r) → ctr2 r })   
redex? (app (abs s) t) = yes r-red
redex? (abs t) with redex? t
... | yes r = yes (r-abs r)
... | no ctr = no (λ { (r-abs r) → ctr r })


_≪_ : ∀ {Γ a} → Rel (Γ ⊢ a) lzero
t1 ≪ t2 = redex t2 × ∀ (r1 : redex t1) → ∃ (λ (r2 : redex t2) → deg r1 ≺ deg r2)

≪-wf : ∀ {Γ a} → WellFounded (_≪_ {Γ} {a})
≪-wf {Γ} {a} = let
    open Subrelation {A = Γ ⊢ a} ≪⇒< renaming (wellFounded to sub-wf)
    open Inverse-image {A = Γ ⊢ a} rank renaming (wellFounded to ii-wf)
  in sub-wf (ii-wf <-wellFounded)
  where
  open import Data.Nat.Base using (ℕ; suc; _≤_; z≤n; s≤s; _<_; _⊔_)
  open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; ⊔-sel)
  
  type-rank : Type → ℕ
  type-rank (base x) = 0
  type-rank (a ⇒ b) = suc (type-rank a ⊔ type-rank b)

  deg-rank : Degree → ℕ
  deg-rank = type-rank ∘ deg-to-type

  abs-rank : ∀ {Γ a} → Γ ⊢ a → ℕ
  abs-rank (var i) = 0
  abs-rank (app s t) = 0
  abs-rank (abs {a} {b} t) = type-rank (a ⇒ b)
  
  rank : ∀ {Γ a} → Γ ⊢ a → ℕ
  rank (var i) = 0
  rank (app s t) = abs-rank s ⊔ rank s ⊔ rank t
  rank (abs t) = rank t

  0<redex-rank : ∀ {Γ a} {t : Γ ⊢ a} (r : redex t) → 1 ≤ deg-rank (deg r)
  0<redex-rank r with deg r
  ... | a ⇛ b = s≤s z≤n
  
  redex-rank≤rank : ∀ {Γ a} (t : Γ ⊢ a) (r : redex t) → deg-rank (deg r) ≤ rank t
  redex-rank≤rank .(app (abs s) t) (r-red {s = s} {t = t}) = ≤-trans (m≤m⊔n _ (rank s)) (m≤m⊔n _ (rank t))
  redex-rank≤rank (app s t) (r-app₁ r) = ≤-trans (≤-trans (redex-rank≤rank s r) (m≤n⊔m (abs-rank s) (rank s))) (m≤m⊔n _ (rank t))
  redex-rank≤rank (app s t) (r-app₂ r) = ≤-trans (redex-rank≤rank t r) (m≤n⊔m (abs-rank s ⊔ rank s) (rank t))
  redex-rank≤rank (abs t) (r-abs r) = redex-rank≤rank t r

  ⊔-zero : ∀ m n → m ⊔ n ≡ 0 → m ≡ 0 × n ≡ 0
  ⊔-zero 0 0 refl = refl , refl
  ⊔-zero 0 (suc n) ()
  ⊔-zero (suc m) 0 ()
  ⊔-zero (suc m) (suc n) ()
  
  max-rank-redex? : ∀ {Γ a} (t : Γ ⊢ a) → ∃ (λ (r : redex t) → rank t ≡ deg-rank (deg r)) ⊎ (rank t ≡ 0)
  max-rank-redex? (var i) = inj₂ refl
  max-rank-redex? (app s t) with ⊔-sel (abs-rank s ⊔ rank s) (rank t)
  max-rank-redex? (app s t) | inj₁ eq rewrite eq with ⊔-sel (abs-rank s) (rank s)
  max-rank-redex? (app s t) | inj₁ eq | inj₁ eq2 rewrite eq2 with s
  ... | var _ = inj₂ refl
  ... | app _ _ = inj₂ refl
  ... | abs s' = inj₁ (r-red , refl)
  max-rank-redex? (app s t) | inj₁ eq | inj₂ eq2 rewrite eq2 with max-rank-redex? s
  ... | inj₁ (r , eq3) = inj₁ (r-app₁ r , eq3)
  ... | inj₂ eq3 = inj₂ eq3
  max-rank-redex? (app s t) | inj₂ eq rewrite eq with max-rank-redex? t
  ... | inj₁ (r , eq2) = inj₁ (r-app₂ r , eq2)
  ... | inj₂ eq2 = inj₂ eq2
  max-rank-redex? (abs t) with max-rank-redex? t
  ... | inj₁ (r , eq) = inj₁ (r-abs r , eq)
  ... | inj₂ eq = inj₂ eq

  ≺ₜ⇒< : ∀ {a1 a2} → a1 ≺ₜ a2 → type-rank a1 < type-rank a2
  ≺ₜ⇒< {.a} {a ⇒ b} left = s≤s (m≤m⊔n (type-rank a) (type-rank b))
  ≺ₜ⇒< {.b} {a ⇒ b} right = s≤s (m≤n⊔m (type-rank a) (type-rank b))

  ≪⇒< : ∀ {Γ a} → {t1 t2 : Γ ⊢ a} → t1 ≪ t2 → rank t1 < rank t2
  ≪⇒< {t1 = t1} {t2 = t2} (r , f) with max-rank-redex? t1
  ... | inj₁ (r1 , eq) rewrite eq = let (r2 , le) = f r1 in ≤-trans (≺ₜ⇒< le) (redex-rank≤rank t2 r2)
  ... | inj₂ eq rewrite eq = ≤-trans (0<redex-rank r) (redex-rank≤rank t2 r)


normalizable : ∀ {Γ a} (t : Γ ⊢ a) → Set
normalizable t = ∃ (λ t' → normal t' × t →β* t')
  
-- aka weak normalization theorem
normalize : ∀ {Γ a} (t : Γ ⊢ a) → normalizable t
normalize = All.wfRec ≪-wf lzero normalizable step
  where
  step : WfRec _≪_ normalizable ⊆′ normalizable
  step t with redex? t
  ... | yes r = λ g → let (t' , ctr , ps) = g (βP-reduce* t) (r , star-deg t) in t' , ctr , (→βP⊂→β* (βP-red* t)) ◅◅ ps
  ... | no ctr = λ _ → t , ctr , ε
  
