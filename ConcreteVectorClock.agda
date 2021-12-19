open import VectorNat as VecNat renaming(_<_ to _<ᵛ_; _≤_ to _≤ᵛ_)
open import Data.Nat as Nat hiding (_<_;_≤_) 
open import Data.Nat.Properties as NatProp 
open import Data.Fin as Fin hiding (_≺_ ;_+_ ;_<_;_≤_;_≤?_;_<?_)
open import Data.Vec hiding (init)
open import Relation.Binary.PropositionalEquality using (_≢_;_≡_;refl; subst;inspect;[_];sym;cong)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Data.Product using (_×_;∃-syntax;_,_;proj₁;proj₂)
open import Data.Bool using (true;false)
open import Relation.Nullary using (Dec; _because_ ; ofⁿ; ofʸ;¬_ )

module ConcreteVectorClock (l : ℕ) where

    
Pid = Fin (suc l)  

open import Event Pid
open import AbstractVectorClock Pid

private 
  variable 
    p q r : Pid
    vc  : VC p
    vc′ : VC q
    vc″ : VC r
 


postulate
-- axiom: if two VCs are from the same process, then either one is less than the other or they are the same VC.
  processTotalOrder : (vc vc′ : VC p) → vc < vc′ ⊎ vc′ < vc ⊎ vc ≡ vc′
  

concrete : VC p → Vec ℕ (suc l)
concrete {p} (init) = incAt p (fillZero (suc l))
concrete {p} (tick vc) = incAt p (concrete vc)
concrete  {p} (merge vc vc′)  = incAt p (max (concrete vc) (concrete vc′))


-- every concrete vc has an incremented index 
∃v[concrete[vc]≡incAt[v,p]] : { vc : VC p} → ∃[ v ] concrete vc ≡ incAt p v
∃v[concrete[vc]≡incAt[v,p]] {vc = init} =    fillZero (suc l) , refl
∃v[concrete[vc]≡incAt[v,p]] {vc = tick vc} =  (concrete vc) , refl
∃v[concrete[vc]≡incAt[v,p]] {vc = merge vc vc₁} = (max (concrete vc) (concrete vc₁)) , refl


data _<ᶜ_ : VC p → VC q → Set where
  crt<crt  : (concrete vc) <ᵛ (concrete vc′) → vc <ᶜ vc′
  

vc<ᶜtick[vc] : vc <ᶜ tick vc
vc<ᶜtick[vc]   =  crt<crt   v<incAt[i,v]

vc<ᶜmerge[vc,vc′] : vc  <ᶜ merge vc vc′
vc<ᶜmerge[vc,vc′]  =  crt<crt  (≤,<→< v≤max[v,v′] v<incAt[i,v])

vc<ᶜmerge[vc′,vc] : vc  <ᶜ merge vc′ vc
vc<ᶜmerge[vc′,vc] {vc′ = vc′}  =  crt<crt  (≤,<→< (v≤max[v′,v] {v′ = (concrete vc′)}) v<incAt[i,v])


<ᶜ→<ᵛ :  vc <ᶜ vc′ →  (concrete vc) <ᵛ (concrete vc′)
<ᶜ→<ᵛ  (crt<crt  v<ᵛv′)  = v<ᵛv′

<ᶜ-transitive  :  vc <ᶜ vc′ → vc′ <ᶜ vc″ → vc <ᶜ vc″
<ᶜ-transitive  vc1<ᶜvc2 vc2<ᶜvc3 = crt<crt  (<-transitive  (<ᶜ→<ᵛ   vc1<ᶜvc2) (<ᶜ→<ᵛ  vc2<ᶜvc3))


  
<→<ᶜ : vc < vc′ → vc <ᶜ vc′
<→<ᶜ vc<tick[vc] = vc<ᶜtick[vc]
<→<ᶜ vc<merge[vc,vc′] = vc<ᶜmerge[vc,vc′]
<→<ᶜ vc<merge[vc′,vc] = vc<ᶜmerge[vc′,vc]
<→<ᶜ (transitive  {vc′ = vc′} x x₁) = <ᶜ-transitive {vc′ = vc′} (<→<ᶜ x) (<→<ᶜ x₁)



lemma1  :   {vc : VC p} {vc′ : VC q} → vc < vc′  →  (lookup (concrete vc) q) Nat.< (lookup (concrete vc′) q)
lemma1 {p} {q} {vc} {tick vc}  vc<tick[vc]
  rewrite sym (1+v[i]≡incAt[i,v][i] {v = concrete vc} {i = q})
 = NatProp.≤-refl
lemma1  {p} {q} {vc} {merge vc″ vc′} vc<merge[vc,vc′]
  rewrite sym (1+v[i]≡incAt[i,v][i] {v = max (concrete vc″) (concrete vc′) } {i = q} )
  = s≤s (v[i]≤max[v,v′][i] {v = concrete vc} {q} {concrete vc′})
lemma1  {p} {q} {vc} {merge vc′ vc″} vc<merge[vc′,vc]
  rewrite sym (1+v[i]≡incAt[i,v][i] {v = max (concrete vc′) (concrete vc″) } {i = q} )
  = s≤s (v[i]≤max[v′,v][i] {v = concrete vc} {q} {concrete vc′})
lemma1  {p} {q} {vc} {vc″} (transitive x y) = NatProp.<-transʳ (v≤v′→v[i]≤v′[i] (<→≤ (<ᶜ→<ᵛ  (<→<ᶜ x)))) (lemma1 y)



lemma2 : {vc vc′ : VC p}   →  (lookup (concrete vc) p)  Nat.≤ (lookup (concrete vc′) p) →  vc < vc′ ⊎ vc ≡  vc′ 
lemma2 {p} {vc} {vc′} v[p]≤v′[p]  
    with processTotalOrder vc vc′
... | inj₁  vc<vc′ =  inj₁  vc<vc′
... | inj₂ (inj₂ vc≡vc′) = inj₂ vc≡vc′
... | inj₂ (inj₁ vc>vc′) with () ←  (<⇒≱  (lemma1 vc>vc′))  v[p]≤v′[p] 


lemma3 : {vc : VC p} {vc′ : VC q}  → p ≢ q → (lookup (concrete vc) p)  Nat.≤ (lookup (concrete vc′) p) →  vc < vc′
lemma3 {p} {q} {vc} {init}  p≢q v[p]≤v′[p]
  rewrite i≢i′→incAt[i′,v][i]≡v[i] {v = fillZero (suc l)}  p≢q 
  rewrite fillZero[l][i]≡0 {suc l} {p}
  rewrite proj₂ (∃v[concrete[vc]≡incAt[v,p]] {p} {vc})
  with () ← (≤⇒≯  v[p]≤v′[p]) (0<incAt[i,v][i] {suc l} {p} { proj₁ (∃v[concrete[vc]≡incAt[v,p]] {p} {vc})})
lemma3 {lp} {q} {vc} {tick vc′} p≢q v[p]≤v′[p]
  rewrite i≢i′→incAt[i′,v][i]≡v[i] {v = concrete vc′}  p≢q 
  =   transitive (lemma3 p≢q  v[p]≤v′[p])  vc<tick[vc] 
lemma3 {p} {q} {vc} {merge {q = r} vc′ vc″ } p≢q  v[p]≤v′[p]
  rewrite i≢i′→incAt[i′,v][i]≡v[i] {v = max (concrete vc′) (concrete vc″)}  p≢q
  with (lookup (concrete vc′) p)  ≤? (lookup (concrete vc″) p)
... | true  because ofʸ v′[p]≤v″[p] 
      rewrite v[i]≤v′[i]→max[v,v′][i]≡v′[i] {v = concrete vc′} {p} {concrete vc″} v′[p]≤v″[p] 
      =  transitive (lemma3 p≢q  v[p]≤v′[p])  vc<merge[vc′,vc]
... | false because ofⁿ v′[p]≰v″[p] 
      rewrite v[i]≰v′[i]→max[v,v′][i]≡v[i] {v = concrete vc′} {p} {concrete vc″} v′[p]≰v″[p] 
      with  p Fin.≟ r
...   | false because  ofⁿ  p≢r
        = transitive (lemma3 p≢r v[p]≤v′[p])  vc<merge[vc,vc′]
...   | true because   ofʸ p≡r
        rewrite  sym p≡r
          with lemma2 {vc = vc} {vc′ = vc′} v[p]≤v′[p]
...       | inj₁ vc<vc′ = transitive vc<vc′ vc<merge[vc,vc′]
...       | inj₂ vc≡vc′  rewrite vc≡vc′ =  vc<merge[vc,vc′]




<ᶜ→< : vc <ᶜ vc′ → vc < vc′
<ᶜ→<  {p} {vc} {q} {vc′} (crt<crt v<ᵛv′) 
    with p Fin.≟ q
... | false because ofⁿ  p≢q  = lemma3 p≢q  ( v≤v′→v[i]≤v′[i] (VecNat.<→≤  v<ᵛv′))
... | true because  ofʸ p≡q 
      rewrite p≡q
      with lemma2  ( v≤v′→v[i]≤v′[i]  (VecNat.<→≤  v<ᵛv′))
...   | inj₁ vc<vc′ = vc<vc′
...   | inj₂ vc≡vc′  with () ← (VecNat.<→≢ v<ᵛv′)(cong concrete vc≡vc′)

