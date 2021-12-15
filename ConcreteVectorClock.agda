open import VectorNat renaming (_<_ to _<′_;_≤_ to _≤′_;<-asymmetric to <′-asymmetric)
open import Data.Nat as Nat hiding (_<_;_<′_;_≤′_) renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties as NatProp using (<⇒≱;≤⇒≯;≤⇒≤ᵇ;≤-trans)
open import Data.Fin as Fin hiding (_≺_ ;_+_ ;_<_;_≤_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec hiding (init)
open import Relation.Binary.PropositionalEquality using (_≢_;_≡_;refl; subst;inspect;[_];sym;cong)
open import Data.Empty using (⊥)
open import Data.Sum
open import Data.Product
open import Data.List.NonEmpty as NonEmpty using (_∷⁺_;List⁺;toList)
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
    h : List⁺ (VC p)
 


postulate
-- axiom
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
  v<ᶜv  : (concrete vc) <′ (concrete vc′) → vc <ᶜ vc′
  

vc<ᶜtick[vc] : vc <ᶜ tick vc
vc<ᶜtick[vc]   =  v<ᶜv   v<incAt[i,v]

vc<ᶜmerge[vc,vc′] : vc  <ᶜ merge vc vc′
vc<ᶜmerge[vc,vc′]  =  v<ᶜv  (≤,<→< v≤max[v,v′] v<incAt[i,v])

vc<ᶜmerge[vc′,vc] : vc  <ᶜ merge vc′ vc
vc<ᶜmerge[vc′,vc] {vc′ = vc′}  =  v<ᶜv  (≤,<→< (v≤max[v′,v] {v′ = (concrete vc′)}) v<incAt[i,v])


<ᶜ→<′ :  vc <ᶜ vc′ →  (concrete vc) <′ (concrete vc′)
<ᶜ→<′ (v<ᶜv  v<′v′)  = v<′v′

<ᶜ-transitive  :  vc <ᶜ vc′ → vc′ <ᶜ vc″ → vc <ᶜ vc″
<ᶜ-transitive  vc1<ᶜvc2 vc2<ᶜvc3 = v<ᶜv  (<-transitive  (<ᶜ→<′  vc1<ᶜvc2) ( <ᶜ→<′ vc2<ᶜvc3))


  
<→<ᶜ : (vc < vc′) → (vc <ᶜ vc′)
<→<ᶜ vc<tick[vc] = vc<ᶜtick[vc]
<→<ᶜ vc<merge[vc,vc′] = vc<ᶜmerge[vc,vc′]
<→<ᶜ vc<merge[vc′,vc] = vc<ᶜmerge[vc′,vc]
<→<ᶜ (transitive  {vc′ = vc′} x x₁) = <ᶜ-transitive {vc′ = vc′} (<→<ᶜ x) (<→<ᶜ x₁)



lemma1a  :   {vc : VC p} {vc′ : VC q} → vc < vc′  →  (lookup (concrete vc) q) Nat.< (lookup (concrete vc′) q)
lemma1a {p} {q} {vc} {tick vc}  vc<tick[vc]
  rewrite sym (1+v[i]≡incAt[i,v][i] {v = concrete vc} {i = q})
 = NatProp.≤-refl
lemma1a  {p} {q} {vc} {merge vc vc′} vc<merge[vc,vc′]
  rewrite sym (1+v[i]≡incAt[i,v][i] {v = max (concrete vc) (concrete vc′) } {i = q} )
  = s≤s (v[i]≤max[v,v′][i] {v = concrete vc} {q} {concrete vc′})
lemma1a  {p} {q} {vc} {merge vc′ vc} vc<merge[vc′,vc]
  rewrite sym (1+v[i]≡incAt[i,v][i] {v = max (concrete vc′) (concrete vc) } {i = q} )
  = s≤s (v[i]≤max[v′,v][i] {v = concrete vc} {q} {concrete vc′})
lemma1a  {p} {q} {vc} {vc″} (transitive x y) = NatProp.<-transʳ (v≤v′→v[i]≤v′[i] (<→≤ (<ᶜ→<′ (<→<ᶜ x)))) (lemma1a y)


lemma1 : {vc vc′ : VC p}   →  (lookup (concrete vc) p)  ≤ⁿ (lookup (concrete vc′) p) →  vc < vc′ ⊎ vc ≡  vc′ 
lemma1 {p} {vc} {vc′} v[p]≤v′[p]  with processTotalOrder vc vc′
... | inj₁  vc<vc′ =  inj₁  vc<vc′
... | inj₂ (inj₂ vc≡vc′) = inj₂ vc≡vc′
... | inj₂ (inj₁ vc>vc′) with () ←  (<⇒≱  (lemma1a vc>vc′))  v[p]≤v′[p] 


lemma2 : {vc : VC p} {vc′ : VC q}  → p ≢ q → (lookup (concrete vc) p)  ≤ⁿ (lookup (concrete vc′) p) →  vc < vc′
lemma2 {zero} {zero} {vc} {vc′}  p≢q v[p]≤v′[p]  with () ← p≢q refl
lemma2 {p} {q} {vc} {init}  p≢q v[p]≤v′[p]
  rewrite i≢i′→incAt[i′,v][i]≡v[i] {v = fillZero (suc l)}  p≢q 
  rewrite fillZero[l][p]≡0 {suc l} {p}
  rewrite proj₂ (∃v[concrete[vc]≡incAt[v,p]] {p} {vc})
  with () ← (≤⇒≯  v[p]≤v′[p]) (0<incAt[i,v][i] {suc l} {p} { proj₁ (∃v[concrete[vc]≡incAt[v,p]] {p} {vc})})
lemma2 {p} {q} {vc} {tick vc′} p≢q v[p]≤v′[p]
  rewrite i≢i′→incAt[i′,v][i]≡v[i] {v = concrete vc′}  p≢q 
  =   transitive (lemma2 p≢q  v[p]≤v′[p])  vc<tick[vc] 
lemma2 {p} {q} {vc} {merge {q = r} vc′ vc″ } p≢q  v[p]≤v′[p]
  rewrite i≢i′→incAt[i′,v][i]≡v[i] {v = max (concrete vc′) (concrete vc″)}  p≢q
  with (lookup (concrete vc′) p)  ≤ᵇ (lookup (concrete vc″) p) | inspect ((lookup (concrete vc′) p)  ≤ᵇ_) (lookup (concrete vc″) p) 
... | true | [ v[p]≤ᵇv′[p] ] 
      rewrite v[i]≤ᵇv′[i]→max[v,v′][i]≡v′[i] {v = concrete vc′} {p} {concrete vc″} v[p]≤ᵇv′[p]
      =  transitive (lemma2 p≢q  v[p]≤v′[p])  vc<merge[vc′,vc]
... | false | [ v[p]≰ᵇv′[p] ]
        with  p Fin.≟ r
...     | false because  ofⁿ  p≢r
          rewrite v[i]≰ᵇv′[i]→max[v,v′][i]≡v[i] {v = concrete vc′} {p} {concrete vc″} v[p]≰ᵇv′[p]
          = transitive (lemma2 p≢r v[p]≤v′[p])  vc<merge[vc,vc′]
...     | true because   ofʸ p≡r
          rewrite  v[i]≰ᵇv′[i]→max[v,v′][i]≡v[i]  {v = concrete vc′} {p} {concrete vc″} v[p]≰ᵇv′[p]
          rewrite  sym p≡r
            with lemma1 {vc = vc} {vc′ = vc′} v[p]≤v′[p]
...         | inj₁ vc<vc′ = transitive vc<vc′ vc<merge[vc,vc′]
...         | inj₂ vc≡vc′  rewrite vc≡vc′ =  vc<merge[vc,vc′]




<ᶜ→< : vc <ᶜ vc′ → (vc < vc′) 
<ᶜ→<  {p} {vc} {q} {vc′} (v<ᶜv  v<′v′) with p Fin.≟ q
... | false because ofⁿ  p≢q  = lemma2 p≢q  ( v≤v′→v[i]≤v′[i] (<→≤  v<′v′))
... | true because  ofʸ p≡q rewrite p≡q
      with lemma1  ( v≤v′→v[i]≤v′[i]  (<→≤  v<′v′))
...   | inj₁ vc<vc′ = vc<vc′
...   | inj₂ vc≡vc′  with () ← (<→≢ v<′v′)(cong concrete vc≡vc′)
