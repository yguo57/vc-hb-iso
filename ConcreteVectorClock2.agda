open import VectorNat renaming (_<_ to _<′_;_≤_ to _≤′_)
open import Data.Nat as Nat hiding (_<_;_<′_;_≤′_) renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (<⇒≱;≤⇒≯)
open import Data.Fin as Fin hiding (_≺_ ;_+_ ;_<_;_≤_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec hiding (init)
open import Relation.Binary.PropositionalEquality using (_≢_;_≡_;refl; subst;inspect;[_];sym;cong)
open import Data.Empty using (⊥)
open import Data.Sum
open import Data.Product
open import Data.List.NonEmpty as NonEmpty using (_∷⁺_;List⁺;toList)
open import Data.Bool using (true;false)

module ConcreteVectorClock2 (l : ℕ) where

    
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
 
-- -- guarantees a correct total order event history of a process
-- data Process : (p : Pid) → List⁺ (VC p) → Set where
--  initProc : Process p NonEmpty.[ init ]
--  tickProc :  Process p h →  Process p  (tick (NonEmpty.head h) ∷⁺ h)
--  mergeProc :    Process p h →  Process p  (merge vc (NonEmpty.head h) ∷⁺ h)

-- data Execution : Pid  →  Set where
--   emptyExec : Execution zero
--   addProc : {n : ℕ} {ls: suc n < suc l} → Process (fromℕ< n ls) h → Execution (fromℕ< n ls) → Execution (suc n)

-- data _follows_ : (VC p) → (VC p) → Set where
--   tickSuc : (tick vc) follows vc 
--   mergeSuc : (merge vc vc′) follows vc′
--   transSuc : vc′ follows vc → vc″ follows vc′ → vc″ follows vc



-- _∈⁺_ : {A : Set} (a : A) → List⁺ A → Set
-- _∈⁺_ a l = a ∈ (NonEmpty.toList l)

postulate
  -- if any two events have the same Pid, then there must be a process that contains them both 
  -- processConsistency : (vc vc′ : VC p) → ∃[ h ] (Process p h × vc ∈⁺ h × vc′ ∈⁺ h)
  -- processConsistency : (vc vc′ : VC p) → vc follows vc′ ⊎ vc′ follows vc
  processTotalOrder : (vc vc′ : VC p) → vc < vc′ ⊎ vc′ < vc ⊎ vc ≡ vc′
  

concrete : VC p → Vec ℕ (suc l)
concrete {p} (init) = incAt p (fillZero (suc l))
concrete {p} (tick vc) = incAt p (concrete vc)
concrete  {p} (merge vc vc′)  = incAt p (max (concrete vc) (concrete vc′))


-- every concrete vc equals some vector incremented at one index
∃v[concrete[vc]≡incAt[v,p]] : { vc : VC p} → ∃[ v ] concrete vc ≡ incAt p v
∃v[concrete[vc]≡incAt[v,p]] {vc = init} =    fillZero (suc l) , refl
∃v[concrete[vc]≡incAt[v,p]] {vc = tick vc} =  (concrete vc) , refl
∃v[concrete[vc]≡incAt[v,p]] {vc = merge vc vc₁} = (max (concrete vc) (concrete vc₁)) , refl

-- uniqueVC : concrete vc ≡ concrete vc′ → vc ≡ vc′
-- uniqueVC {vc = init} {vc′ = init} eq = refl
-- uniqueVC {vc = init} {vc′ cx= tick vc′} eq = {!!}
--   where
--     fillZero≡concrete = incAt-inv eq
-- uniqueVC {vc = init} {vc′ = merge  vc″ vc′} eq = {!!}
-- uniqueVC {vc = tick vc} {vc′ = vc′} eq = {!!}
-- uniqueVC {vc = merge vc vc₁} {vc′ = vc′} eq = {!!}

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


mergeSameP≡tickˡ : {vc vc′ : VC p } →  vc <ᶜ vc′ → concrete (tick vc′) ≡ concrete (merge vc vc′)
mergeSameP≡tickˡ  {vc = vc} {vc′ = vc′} vc<ᶜvc′ 
  with  v<ᶜv  concrete[vc]<′concrete[vc′] ← vc<ᶜvc′ 
  rewrite sym(max-absorptionˡ (<→≤ concrete[vc]<′concrete[vc′])) = refl

mergeSameP≡tickʳ  : {vc vc′ : VC p } →  vc <ᶜ vc′ → concrete (tick vc′) ≡ concrete (merge vc′ vc)
mergeSameP≡tickʳ {vc = vc} {vc′ = vc′} vc<ᶜvc′ 
  with  v<ᶜv  concrete[vc]<′concrete[vc′] ← vc<ᶜvc′ 
  rewrite sym(max-absorptionʳ (<→≤ concrete[vc]<′concrete[vc′])) = refl

<→<ᶜ : (vc < vc′) → (vc <ᶜ vc′)
<→<ᶜ vc<tick[vc] = vc<ᶜtick[vc]
<→<ᶜ vc<merge[vc,vc′] = vc<ᶜmerge[vc,vc′]
<→<ᶜ vc<merge[vc′,vc] = vc<ᶜmerge[vc′,vc]
<→<ᶜ (transitive  {vc′ = vc′} x x₁) = <ᶜ-transitive {vc′ = vc′} (<→<ᶜ x) (<→<ᶜ x₁)








<ᶜ→<₁ :  {vc vc′ : VC p} → vc <ᶜ vc′ → (vc < vc′)  
<ᶜ→<₁ {p} {vc} {vc′} (v<ᶜv  v<′v′)  with processTotalOrder vc vc′ 
...                               | inj₁ vc<vc′ = vc<vc′
...                               | inj₂ (inj₂ vc′≡vc) with () ← ((<→≢  v<′v′) (cong concrete vc′≡vc))
...                               | inj₂ (inj₁ vc′<vc) with (<→<ᶜ vc′<vc)
...                                                    | v<ᶜv  v′<′v  with () ← <-irreflexive v<′v′ v′<′v 



lemma1 : {vc : VC p} {vc′ : VC q}  → p ≢ q → (lookup (concrete vc) p)  ≤ⁿ (lookup (concrete vc′) p) →  vc < vc′
lemma1 {zero} {zero} {vc} {vc′}  p≢q v[p]≤v′[p]  with () ← p≢q refl
lemma1 {p} {q} {vc} {init}  p≢q v[p]≤v′[p]
  rewrite p≢q→incAt[q,v][p]≡v[p] {v = fillZero (suc l)}  p≢q 
  rewrite fillZero[l][p]≡0 {suc l} {p}
  rewrite proj₂ (∃v[concrete[vc]≡incAt[v,p]] {p} {vc})
  with () ← (≤⇒≯  v[p]≤v′[p]) (0<incAt[i,v][p] {suc l} {p} { proj₁ (∃v[concrete[vc]≡incAt[v,p]] {p} {vc})})
lemma1 {p} {q} {vc} {tick vc′} p≢q v[p]≤v′[p]
  rewrite p≢q→incAt[q,v][p]≡v[p] {v = concrete vc′}  p≢q 
  =   transitive (lemma1 p≢q  v[p]≤v′[p])  vc<tick[vc] 
lemma1 {p} {q} {vc} {merge vc′ vc″} p≢q vc≤vc′
  rewrite p≢q→incAt[q,v][p]≡v[p] {v = max (concrete vc′) (concrete vc″)}  p≢q
  with (lookup (concrete vc) p)  ≤ᵇ (lookup (concrete vc′) p)
... | true = {!!}
... | false = {!!}


<ᶜ→<₂ :  {vc : VC p} { vc′ : VC q}  → p ≢ q → vc <ᶜ vc′ → (vc < vc′) 
<ᶜ→<₂ {p} {q} {vc} {vc′} p≢q (v<ᶜv x) = {!!}
