module LC.ChurchRosser where

open import LC.Term
open import LC.Beta
open import Data.Product using (∃; _×_; _,_)

star-lemma : ∀ {Γ} {t t' : Term Γ} → t →βP t' → t' →βP βP-reduce* t
star-lemma (βP-red p p₁) = ⟦⟧-βP (star-lemma p) (star-lemma p₁)
star-lemma (βP-var i) = βP-var i
star-lemma (βP-app {t1 = var _} p p₁) = βP-app (star-lemma p) (star-lemma p₁)
star-lemma (βP-app {t1 = app _ _} p p₁) = βP-app (star-lemma p) (star-lemma p₁)
star-lemma (βP-app {t1 = abs _} (βP-abs p) p₁) = βP-red (star-lemma p) (star-lemma p₁)
star-lemma (βP-abs p) = βP-abs (star-lemma p)

SemiConfluent : ∀ {A : Set} → (A → A → Set) → Set
SemiConfluent R = ∀ {t t₁ t₂} → R t t₁ → Star R t t₂ → ∃ (λ s → Star R t₁ s × Star R t₂ s)
 
βP-semiconfluence : ∀ {Γ} → SemiConfluent (_→βP_ {Γ})
βP-semiconfluence {t₁ = t₁} p ε = t₁ , (ε , p ◅ ε)
βP-semiconfluence p₁ (p₂ ◅ ps) =
   let
     p₁' = star-lemma p₂
     p₂' = star-lemma p₁
     t' , (ps' , ps₁) = βP-semiconfluence p₁' ps
   in
     t' , (p₂' ◅ ps' , ps₁)
 
Confluent : ∀ {A : Set} → (A → A → Set) → Set
Confluent R = ∀ {t t₁ t₂} → Star R t t₁ → Star R t t₂ → ∃ (λ s → Star R t₁ s × Star R t₂ s)

βP-confluence : ∀ {Γ} → Confluent (_→βP_ {Γ})
βP-confluence {t₂ = t₂} ε ps = t₂ , (ps , ε)
βP-confluence (p ◅ ps₁) ps₂ =
  let
    t' , (ps₂' , ps') = βP-semiconfluence p ps₂
    t'' , (ps₂'' , ps₁') = βP-confluence ps₁ ps₂'
  in
    t'' , (ps₂'' , ps' ◅◅ ps₁')

β-confluence : ∀ {Γ} → Confluent (_→β_ {Γ})
β-confluence ps₁ ps₂ =
  let t' , (ps₂' , ps₁') = βP-confluence (→β*⊂→βP* ps₁) (→β*⊂→βP* ps₂)
  in t' , (→βP*⊂→β* ps₂' , →βP*⊂→β* ps₁')
