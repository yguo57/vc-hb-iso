module VectorNat where
open import Data.Vec hiding (init)
open import Data.Nat as Nat hiding (_<_;_≤_) 
open import Data.Nat.Properties
open import Data.Fin  hiding (_≺_ ;_+_ ;_<_;_≤_;_≟_;pred)
open import Data.Bool hiding (_<_;_≤_;_≟_)
open import Data.Product
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_;refl;inspect;[_];subst;sym;cong;cong₂)






private
  variable
   a b c l : ℕ
   v v′ v″ : Vec ℕ l
   i i′ i″ : Fin l

data _≤_ : {l : ℕ } → (Vec ℕ l) → (Vec ℕ  l) →  Set where
    []≤[] : [] ≤ []
    ∷≤∷ : (a ≤ᵇ b) ≡ true → v ≤ v′ → (a ∷  v) ≤ ( b ∷  v′)

-- data _<_ : {l : ℕ } → (Vec ℕ l) → (Vec ℕ l) →  Set where
--         t<t :  (a ≤ᵇ b) ≡ true → v < v′ → (a ∷ v) < ( b ∷ v′)
--         h<h :  (a <ᵇ b) ≡ true → v ≤ v′ → (a ∷ v) < ( b ∷ v′)

data _<_ : {l : ℕ } → (Vec ℕ l) → (Vec ℕ l) →  Set where
        t<t :  (a ≤ᵇ b) ≡ true →  _<_ {l} v v′ → _<_ {suc l} (a ∷ v) ( b ∷ v′)
        h<h :  (a <ᵇ b) ≡ true → _≤_ {l} v  v′ → _<_ {suc l} (a ∷ v) ( b ∷ v′)

-- helper functions
fillZero : (l : ℕ)  → Vec ℕ l 
fillZero zero = [] 
fillZero (suc m) =  0 ∷ (fillZero m)

incAt : Fin l →  Vec ℕ l → Vec ℕ l
incAt zero   (x ∷ xs)  = (suc x) ∷ xs
incAt (suc i) (x ∷ xs) = x ∷ (incAt i xs)

max : Vec ℕ  l → Vec ℕ l → Vec ℕ l 
max  (x ∷ xs)  (y ∷ ys)  with x ≤ᵇ y 
...                       | true   = y ∷ (max xs ys)
...                       | false  = x ∷ (max xs ys)
max [] [] = []

-- lemmas about ≤ᵇ and <ᵇ
postulate
    <ᵇ-transitive : (a <ᵇ b) ≡ true →  (b <ᵇ c) ≡ true  → (a <ᵇ c) ≡ true
    ≤ᵇ-transitive : (a ≤ᵇ b) ≡ true →  (b ≤ᵇ c) ≡ true  →  (a ≤ᵇ c) ≡ true
    ≤ᵇ,<ᵇ→<ᵇ : (a ≤ᵇ b) ≡ true →  (b <ᵇ c) ≡ true  →  (a <ᵇ c) ≡ true
    <ᵇ,≤ᵇ→<ᵇ : (a <ᵇ b) ≡ true →  (b ≤ᵇ c) ≡ true  →  (a <ᵇ c) ≡ true
    <ᵇ→≤ᵇ : (a <ᵇ b) ≡ true → (a ≤ᵇ b) ≡ true
    ≤ᵇ→not>ᵇ :  {bl : Bool} → (a ≤ᵇ b) ≡ bl → (b <ᵇ a) ≡ not bl
    ≤ᵇtrue,≥ᵇtrue→≡ : (a ≤ᵇ b) ≡ true → (b ≤ᵇ a) ≡ true → a ≡ b
    ≤ᵇ-reflexive : (a ≤ᵇ a) ≡ true

<ᵇ-irreflexive : (a <ᵇ b) ≡ true →  (b <ᵇ a) ≡ true → ⊥
<ᵇ-irreflexive {a} {b} eq₁ eq₂ with contra  ← ≤ᵇ→not>ᵇ {a} {b} (<ᵇ→≤ᵇ {a} {b} eq₁ ) | b <ᵇ a
... | false with () ← eq₂ 
... | true with () ← contra

<ᵇ-inv-suc :  (suc a <ᵇ suc b) ≡ true → (a <ᵇ b) ≡ true
<ᵇ-inv-suc {a} {b} lb with (suc a <ᵇ suc b) 
... | true = refl
≤ᵇ-inv-suc :  (suc a ≤ᵇ suc b) ≡ true → (a ≤ᵇ b) ≡ true
≤ᵇ-inv-suc {zero} {b} refl = refl
≤ᵇ-inv-suc {suc a} {b} leb = leb

a<ᵇsa≡true : (a <ᵇ suc a) ≡ true
a<ᵇsa≡true {zero} = refl
a<ᵇsa≡true {suc n} =  a<ᵇsa≡true {n}

a≤ᵇa≡true : (a ≤ᵇ a) ≡ true
a≤ᵇa≡true {zero} = refl
a≤ᵇa≡true {suc n} = a<ᵇsa≡true {n}


-- lemmas about _<_ and _≤_

v≤v : v ≤ v
v≤v {_} {[]} = []≤[]
v≤v {_} {(x ∷ xs)} = ∷≤∷ (a≤ᵇa≡true {x}) v≤v


≤-transitive : v ≤ v′ → v′ ≤ v″  → v ≤ v″
≤-transitive ([]≤[]) ([]≤[]) = []≤[]
≤-transitive (∷≤∷ {a} {b} a≤ᵇb v≤v′) (∷≤∷ {b} {c} b≤ᵇc v′≤v″) =  ∷≤∷ (≤ᵇ-transitive  {a} {b} {c} a≤ᵇb  b≤ᵇc) (≤-transitive v≤v′ v′≤v″)

<→≤ : v < v′ → v ≤ v′
<→≤ (t<t x y) = ∷≤∷ x (<→≤  y)
<→≤ (h<h {a} {b}  x y) = ∷≤∷ (<ᵇ→≤ᵇ {a} {b}  x) y

<-transitive : v < v′ → v′ < v″  → v < v″
<-transitive (t<t {a} {b} a≤ᵇb  v<v′) (t<t {b} {c} b≤ᵇc  v′<v″) = t<t ( ≤ᵇ-transitive {a} {b} {c} a≤ᵇb  b≤ᵇc ) ( <-transitive  v<v′ v′<v″)
<-transitive (t<t  {a} {b} a≤ᵇb  v<v′) (h<h  {b} {c}  b<ᵇc  v′≤v″) = h<h ( ≤ᵇ,<ᵇ→<ᵇ {a} {b} {c}  a≤ᵇb  b<ᵇc ) (≤-transitive ( <→≤  v<v′)  v′≤v″)
<-transitive (h<h  {a} {b} a<ᵇb  v≤v′) (t<t {b} {c} b≤ᵇc  v′<v″) = h<h ( <ᵇ,≤ᵇ→<ᵇ {a} {b} {c} a<ᵇb b≤ᵇc) (≤-transitive v≤v′ ( <→≤  v′<v″))
<-transitive (h<h  {a} {b} a<ᵇb  v≤v′) (h<h {b} {c} b<ᵇc  v′≤v″) = h<h (<ᵇ-transitive {a} {b} {c} a<ᵇb b<ᵇc) (≤-transitive v≤v′  v′≤v″)



≤,<→< : v ≤ v′ → v′ < v″  → v < v″
≤,<→< (∷≤∷ {a} {b} a≤ᵇb  v≤v′  ) (t<t {b} {c} b≤ᵇc  v′<v″) = t<t (≤ᵇ-transitive {a} {b} {c} a≤ᵇb  b≤ᵇc) ( ≤,<→< v≤v′ v′<v″)
≤,<→< (∷≤∷ {a} {b} a≤ᵇb  v≤v′) (h<h {b} {c} b<ᵇc  v′≤v″) = h<h (≤ᵇ,<ᵇ→<ᵇ {a} {b} {c} a≤ᵇb b<ᵇc) ( ≤-transitive v≤v′ v′≤v″)

<→¬≤ :  v < v′ → v′ ≤ v → ⊥ 
<→¬≤ {v = x ∷ xs} {v′ = y ∷ ys}  (h<h x<y _) (∷≤∷ y≤x _ ) rewrite (≤ᵇ→not>ᵇ {y}{x} y≤x) with () ← x<y 
<→¬≤ {v = x ∷ xs} {v′ = y ∷ ys}  (t<t _ xs<ys) (∷≤∷ _ ys≤xs ) = <→¬≤ xs<ys ys≤xs

<-irreflexive :  v < v′ → v′ < v → ⊥ 
<-irreflexive v<v′ v′<v =  <→¬≤ v′<v (<→≤ v<v′)


<→≢ : v < v′ → v ≢ v′
<→≢ {v = (a ∷ as)} {b ∷ bs} (t<t _ as<bs) = λ v≡v′ → (<→≢ as<bs )(cong tail v≡v′)
<→≢ {v = (a ∷ as)} {b ∷ bs} (h<h a<ᵇb≡true _ ) = λ v≡v′ → <⇒≢ (<ᵇ⇒< a b (≡→T  a<ᵇb≡true)) ( cong head v≡v′)
  where ≡→T : ∀ {b : Bool} → b ≡ true → T b
        ≡→T refl  =  tt


-- lemmas about fillZero
fillZero-least : ¬  v < fillZero l  
fillZero-least (t<t _ t) = fillZero-least t


fillZero[l][p]≡0 :  lookup (fillZero l) i ≡ 0
fillZero[l][p]≡0 {suc l} {zero} = refl
fillZero[l][p]≡0 {suc l} {suc i} = fillZero[l][p]≡0 {l} {i}


--lemmas about incAt
incAt-inv : incAt i v ≡ incAt i v′ → v ≡ v′
incAt-inv {i = zero} {v = x ∷ v} {v′ = y ∷ v′} eq =  cong₂ _∷_ x≡y v≡v′ 
  where
    x≡y = cong pred (cong head eq)
    v≡v′ = cong tail eq
incAt-inv {i = suc i} {v = x ∷ v} {v′ = y  ∷ v′} eq = cong₂ _∷_ x≡y v≡v′
 where
    x≡y = cong head eq
    v≡v′ = incAt-inv {i = i} {v = v} {v′ = v′} (cong tail eq) 

v<incAt[i,v] : v < incAt i v
v<incAt[i,v] {_} {(x ∷ xs)} {zero} = h<h (a<ᵇsa≡true {x}) v≤v
v<incAt[i,v] {_} {(x ∷ xs)}{(suc n)} = t<t (a≤ᵇa≡true {x}) v<incAt[i,v]

≤-inv-incAt :  incAt i v ≤ incAt i v′ → v ≤ v′
≤-inv-incAt {i = zero} {x ∷ v} {y ∷ v′} (∷≤∷ sx≤sy v≤v′) = ∷≤∷ (≤ᵇ-inv-suc {x} {y} sx≤sy)  v≤v′
≤-inv-incAt {i = suc i} {x ∷ v} {y ∷ v′} (∷≤∷ sx≤sy v≤v′) = ∷≤∷ sx≤sy (≤-inv-incAt v≤v′)

<-inv-incAt :  incAt i v < incAt i v′ → v < v′
<-inv-incAt {i = zero} {v = x ∷ v} {v′ = y ∷ v′} (t<t sx≤sy v<v′) = t<t (≤ᵇ-inv-suc {x} {y} sx≤sy) v<v′ 
<-inv-incAt {i = zero} {v = x ∷ v} {v′ = y ∷ v′} (h<h sx<sy v≤v′) =  h<h (<ᵇ-inv-suc {x} {y} sx<sy) v≤v′ 
<-inv-incAt {i = suc i} {v = x ∷ v} {v′ = y ∷ v′} (t<t x≤y v<v′) = t<t x≤y (<-inv-incAt v<v′)
<-inv-incAt {i = suc i} {v = x ∷ v} {v′ = y ∷ v′} (h<h x<y v≤v′) = h<h x<y (≤-inv-incAt v≤v′)


-- lemmas about max
max-comm : max v v′ ≡ max v′ v
max-comm {v = []} {v′ = []} = refl
max-comm {v = x ∷ v} {v′ = y ∷ v′} 
    with x ≤ᵇ y | y ≤ᵇ x | inspect (x ≤ᵇ_) y | inspect (y ≤ᵇ_) x
... | false | true | _ | _  rewrite sym (max-comm {v = v} {v′ = v′}) = refl
... | true | true | [ a ] | [ b ]
      rewrite ≤ᵇtrue,≥ᵇtrue→≡ {x} {y} a b  
      rewrite sym (max-comm {v = v} {v′ = v′})
      = refl
... | true | false | _ | _  rewrite sym (max-comm {v = v} {v′ = v′}) = refl
... | false | false | [ a ] | [ b ]
     rewrite (<ᵇ→≤ᵇ {y} {x} (≤ᵇ→not>ᵇ {x} {y} a))
     = exp b
  where
      exp : ∀ {n} {x : Set n} → true ≡ false → x
      exp ()
max-absorptionˡ : v ≤ v′ → v′ ≡ max v v′
max-absorptionˡ {v = []} {v′ = []} []≤[] = refl
max-absorptionˡ {_} {x ∷ xs} {y ∷ ys} (∷≤∷ x≤ᵇy≡true xs≤ys)  
      with true ← x ≤ᵇ y   
      rewrite sym (max-absorptionˡ xs≤ys) = refl


max-absorptionʳ : v ≤ v′ → v′ ≡ max v′ v
max-absorptionʳ {v = v} {v′ = v′}  v≤v′ rewrite sym (max-comm {v = v} {v′ = v′}) = max-absorptionˡ v≤v′



v≤max[v,v′] : v ≤ max v v′
v≤max[v,v′] {_} {[]} {[]} = []≤[]
v≤max[v,v′] {_} {x ∷ xs} {y ∷ ys}  with  (x ≤ᵇ_) y | inspect (x ≤ᵇ_) y
...                                 | true | [ x≤ᵇy≡true ]  = ∷≤∷  x≤ᵇy≡true  ( v≤max[v,v′] {v = xs } {v′ = ys})
...                                 | false | [ x≤ᵇy≡false ] = ∷≤∷ ( ≤ᵇ-reflexive {x} ) (v≤max[v,v′] {v = xs } {v′ = ys})

v≤max[v′,v] : v ≤ max v′ v
v≤max[v′,v] {_} {[]} {[]} = []≤[]
v≤max[v′,v] {_} {x ∷ xs} {y ∷ ys}  with  (y ≤ᵇ_) x | inspect ( y ≤ᵇ_) x
...                                 | true | [ y≤ᵇx≡true ]  = ∷≤∷ (≤ᵇ-reflexive {x} ) (  v≤max[v′,v] {v = xs} {v′ = ys})
...                                 | false | [ y≤ᵇx≡false ] = ∷≤∷ ( <ᵇ→≤ᵇ  {x} {y} (≤ᵇ→not>ᵇ {y} {x}  y≤ᵇx≡false)) ( ( v≤max[v′,v] {v = xs} {v′ = ys}))


-- lemmas about lookup

v[p]<incAt[i,v][p] : (lookup v i)  Nat.< (lookup (incAt i v ) i)
v[p]<incAt[i,v][p] {v = v@(x ∷ xs) } {zero} with lookup v zero |  lookup (incAt zero v) zero
... | zero | zero = z≤n
... | zero | suc y = s≤s ≤-refl
... | suc x | y =  ≤-refl
v[p]<incAt[i,v][p] {v = v@(x ∷ xs) } {suc i} = v[p]<incAt[i,v][p] {v = xs} {i}

0<incAt[i,v][p] : 0  Nat.< (lookup (incAt i v ) i)
0<incAt[i,v][p] {i = zero} {x ∷ xs} = s≤s z≤n
0<incAt[i,v][p] {i = suc i} {x ∷ xs} = 0<incAt[i,v][p] {i = i} {xs}


p≢q→incAt[q,v][p]≡v[p] : i ≢ i′ →  lookup (incAt i′ v) i ≡ lookup v i
p≢q→incAt[q,v][p]≡v[p] {suc l} {zero} {zero} p≢q with () ←  p≢q refl
p≢q→incAt[q,v][p]≡v[p] {suc l} {zero} {suc q} {x ∷ xs} _ = refl
p≢q→incAt[q,v][p]≡v[p] {suc l} {suc p} {zero}  {x ∷ xs} _ =  refl
p≢q→incAt[q,v][p]≡v[p] {suc l} {suc p} {suc q} {x ∷ v} sp≢sq = p≢q→incAt[q,v][p]≡v[p] {l} {p} {q}  (λ p≡q →  sp≢sq (cong suc p≡q))

v[p]≤ᵇv′[p]→max[v,v′][p]≡v′[p] : (lookup v i)  ≤ᵇ (lookup v′ i) →  lookup (max v v′ ) i ≡ lookup v′
v[p]≤ᵇv′[p]→max[v,v′][p]≡v′[p] = ?
