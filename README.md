# Vector Clock Happens-Before Isomorphism

Tested with Agda 2.6.2, Agda standard library 1.7.

Forked from Gan Shen's isomophism proof between abstract VC less-than and happens-before, where
[VC](https://github.com/yguo57/vc-hb-iso/blob/fd5faa0cfc5bfe96db287a3b64d1e59ab1b8905c/AbstractVectorClock.agda#L10-L18) is essentially defined as a history of updates to the vector clock value. The updates can be of type init, tick (the result of sending a messgae), or merge (the result receiving a message). This VC is also called an abstract VC because the vector underlying it is not part of this data structure. 

To make the vector values explicit, I made a function ```concrete```
```
concrete : VC p → Vec ℕ (suc l)
concrete {p} (init) = incAt p (fillZero (suc l))
concrete {p} (tick vc) = incAt p (concrete vc)
concrete  {p} (merge vc vc′)  = incAt p (max (concrete vc) (concrete vc′))
```
that converts an abstract VC into its vector clock values. I also call this vector generated from an abstract VC the corresponding concrete VC - it is the form actually used in algorithms such as causal broadcast. 
Note that for each VC the index representing their own process starts at 1 (so if vc is of type VC 0, concrete vc = [1,0,0,...]). This is to prevent an initial ConcreteVC value from being less than all other clock values (because [0,0,...0] is less than all other vectors ), which might have no happens-before relation with it.


Then concrete VC less ```_<ᶜ_```then is defined as a wrapper around component wise comparison (```_<ᵛ_```) of two vectors generated from VCs
```
data _<ᶜ_ : VC p → VC q → Set where
  crt<crt  : (concrete vc) <ᵛ (concrete vc′) → vc <ᶜ vc′
```
Because the isomorphism abstract VC less-than and happens-before is already proven , I only need to establish the isomorphism between concrete VC less-than and abstract VC less-than, namely these two theorems
```
<→<ᶜ : vc < vc′ → vc <ᶜ vc′
<ᶜ→< : vc <ᶜ vc′ → vc < vc′
```
The implication from abstract to concrete VC less-than is straightforward: properties of nat vectors can be used to prove theorems about ```_<ᶜ_``` that correspond to each of ```_<_```'s constructors, as shown here. 

The other direction is trickier. Due to how  VC is defined, a contradiction can be derived where for VCs D and E, ¬D<E but D<ᶜE. 
Therefore I need to prevent such cases from happening. One intuitive way is to explicitly define an execution that eliminates anormalies like this, but how should an execution be defined? If we think about what makes at an execution "normal" ,  there are two obvious conditions (there are more, for example each receive event should pair with a send event from another process, but they are not needed for the proof)
    1. the set of all events (and thus their VCs) forms a irreflexive partial order
    2. the set of all events on the same process forms a total order
    In fact, 1 is taken care of by the definition of event (and this also holds for the abstract VC that is ismorphic to it) as proven here, leaving only 2, and it is precisely 2 that is being violated in the counterexample above. To solve this problem without going through the trouble of creatinig an appropriate data structure for execution, I simply define 2 as a postulate
    
```
postulate
-- axiom: if two VCs are from the same process, then either one is less than the other or they are the same VC.
  processTotalOrder : (vc vc′ : VC p) → vc < vc′ ⊎ vc′ < vc ⊎ vc ≡ vc′
```

(this also makes me wonder how to correctly define execution, and whether using execution would add any value to the proof)

With the axiom in place, I split ```<ᶜ→< : vc <ᶜ vc′ → vc < vc′``` into two cases: first when the two VCs are from the same process, so ```processTotalOrder``` can be used, and second when the two VCs are from different processes. 

For the first case,  processTotalOrder states limits the relationship between ```vc``` and ```vc′``` into three possibilities, but given ``` vc <ᶜ vc′```, I can prove that ```vc′ < vc``` is imposssible. (lemma1)

Essentially, ```vc′ < vc``` implies that  ``` vc```  is constructed from ``` vc′``` by a number of ticks and merges, each of which increments its value at p (the index of vc and vc′) , so vc should be greater than vc′ at p  but ``` vc <ᶜ vc′```  implies that ``` vc′``` is greater or equal than ```vc``` at all indexes, which implies  ``` vc′``` is greater or equal than ```vc``` at its index p, including p - a contradiction. 

I use this weaker statement ```(lookup (concrete vc) q)  Nat.≤ (lookup (concrete vc′) q)``` as the premise for lemma2. Now  the possible relationships between  ```vc``` and ```vc′``` can be narrowed down into two -  ``` vc < vc′ ⊎ vc ≡ vc′ ``` when they are on the same process. Since ``` __<ᶜ_ ``` is irreflexive, we do not need to worry about ```vc ≡ vc′``` (lemma2)

Similarly, when vc and vc′ are from different processes (call them p and q), only a weaker premise about a single index that is implied by ``` vc <ᶜ vc′```. In this case it's ```(lookup (concrete vc) p)  Nat.≤ (lookup (concrete vc′) p)``` where p is the index of the smaller vc. Now consider all possible values for ```  vc′ ```

1. when  ```  vc′ = init ```, then concrete vc′ has zero on all indices except q, so lookup (concrete vc′) p = 0, but lookup (concrete vc) p = 1, so ```(lookup (concrete vc) p)  Nat.≤ (lookup (concrete vc′) p)``` leads to a contradiction 

2. when ``` vc′ = tick  vc′```, the premise becomes ```(lookup (concrete vc) p)  Nat.≤ (lookup (concrete (tick vc′)) p)``` . Note that concrete (tick  vc′) only increments concrete ( vc′) on index q, leaving index p untouched, so ``` lookup (concrete (tick  vc′)) p  ≡ lookup (concrete vc′) p ```  and therefore ```(lookup (concrete vc) p)  Nat.≤ (lookup (concrete vc′) p)```. By  induction, ```vc <  vc′'``` ̄, and then by transitivity ```vc < tick vc′ ```

3. When  ```vc′ = merge vc″ vc′``` where  vc″ is on process r, the premise becomes ```(lookup (concrete vc) p)  Nat.≤ (lookup (concrete (merge vc vc′)) p)```.  A merge involves a pointwise maximum , which means between ```vc ``` and ```vc′```,  only the one with the greater value on p contributes to the value on p after the merge. 
   1. If it is ```vc′``` , then we have ```(lookup (concrete vc) p)  Nat.≤ (lookup (concrete vc′)) p)```. By induction ```vc <  vc′```, and by transitivity  ``` vc < merge  vc″ vc′  v ``` 
   2. If it is  ``` vc″```, there are two further cases
      1. If  ``` vc″``` and ```vc``` are from different processes (```p≢r```), then it is the mirror image of the above -  by induction ```vc <  vc″```, and by transitivity ```vc < merge  vc″ vc′ ```
      2. If  ``` vc″``` and  ```vc``` are from the same processes (```p≡r```), then lemma2 is applicable , yielding two more cases
         1. If vc<vc′. Use the same trick - by induction ```vc <  vc′```, and by transitivity ```vc < merge  vc″ vc′ ``` 
         2. If vc≡vc′. Obviously  ``` vc′ < merge vc″ vc′  ```

This concludes the case where vc and vc′ are from different processes (lemma3)

Combining lemma2 and lemma3 gives a complete proof of ``` vc <ᶜ vc′ → vc < vc′ ```
