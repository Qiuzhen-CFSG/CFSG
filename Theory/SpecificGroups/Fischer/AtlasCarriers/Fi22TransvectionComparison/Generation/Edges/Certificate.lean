module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Seeds
/-!
# Checked action tables for Fi22 Schreier-edge factors

An entry carries forward and inverse tables together with a proof that they
act as an element of the actual commuting-conjugate subgroup. Products of
entries retain that property. Thus the numerical checks in the table modules
certify actual subgroup elements, without using a centralizer order or a
labeling-equivariance premise.

The table modules instantiate this interface first with the six certified
seeds and then with short products of earlier entries. The edge certificates
compare products of these entries with the literal Schreier words.

Source: ATLAS F22G1-p3510B0 and the conjugation action following GLS3 Table 5.3t,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate SmallBase

def packedAction (p : Nat) (x : Fin 3510) : Fin 3510 :=
  ⟨(p >>> (12 * x.val)) % 4096 % 3510, Nat.mod_lt _ (by decide)⟩

structure Entry where
  forward : Nat
  backward : Nat
  valid : ∃ g : Carrier, g ∈ commutingConjugateSubgroup ∧
    (∀ x, packedAction forward x = inclusion g x) ∧
    (∀ x, packedAction backward x = inclusion g⁻¹ x)

noncomputable def Entry.element (e : Entry) : Carrier := e.valid.choose

theorem Entry.element_mem (e : Entry) : e.element ∈ commutingConjugateSubgroup :=
  e.valid.choose_spec.1

def Entry.action (e : Entry) (b : Bool) : Fin 3510 → Fin 3510 :=
  packedAction (if b then e.backward else e.forward)

theorem Entry.action_eq (e : Entry) (b : Bool) (x : Fin 3510) :
    e.action b x = inclusion (if b then e.element⁻¹ else e.element) x := by
  cases b
  · exact e.valid.choose_spec.2.1 x
  · exact e.valid.choose_spec.2.2 x

noncomputable def wordElement (w : List (Entry × Bool)) : Carrier :=
  (w.map (fun eb => if eb.2 then eb.1.element⁻¹ else eb.1.element)).prod

def wordAction (w : List (Entry × Bool)) (x : Fin 3510) : Fin 3510 :=
  w.foldr (fun eb y => eb.1.action eb.2 y) x

theorem wordElement_mem (w : List (Entry × Bool)) :
    wordElement w ∈ commutingConjugateSubgroup := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨⟨e, b⟩, _, rfl⟩ := List.mem_map.mp hg
  cases b
  · exact e.element_mem
  · exact Subgroup.inv_mem _ e.element_mem

theorem wordAction_eq (w : List (Entry × Bool)) (x : Fin 3510) :
    wordAction w x = inclusion (wordElement w) x := by
  induction w with
  | nil => rfl
  | cons eb w ih =>
    simpa only [wordAction, wordElement, List.foldr_cons, List.map_cons,
      List.prod_cons, map_mul, Equiv.Perm.mul_apply, Entry.action_eq] using
      congrArg (inclusion (if eb.2 then eb.1.element⁻¹ else eb.1.element)) ih

def ofElement (p q : Nat) (g : Carrier) (hg : g ∈ commutingConjugateSubgroup)
    (hp : ∀ x, packedAction p x = inclusion g x)
    (hq : ∀ x, packedAction p (packedAction q x) = x) : Entry :=
  ⟨p, q, g, hg, hp, fun x => by
    apply (inclusion g).injective
    rw [← hp, hq]
    simp only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply]⟩

noncomputable def ofWord (w : List (Entry × Bool)) (p q : Nat)
    (hp : ∀ x, packedAction p x = wordAction w x)
    (hq : ∀ x, packedAction p (packedAction q x) = x) : Entry :=
  ofElement p q (wordElement w) (wordElement_mem w)
    (fun x => (hp x).trans (wordAction_eq w x)) hq

-- Concrete check predicates keep carrier operations outside kernel evaluation.
def mapCheck (p : Nat) (f : Fin 3510 → Fin 3510) (n : Nat) : Bool :=
  let x : Fin 3510 := ⟨n % 3510, Nat.mod_lt _ (by decide)⟩
  decide (packedAction p x = f x)

theorem mapCheck_sound (p : Nat) (f : Fin 3510 → Fin 3510)
    (h : BitNetwork.check (mapCheck p f) 0 3510 = true) :
    ∀ x, packedAction p x = f x := by
  intro x
  have hx := BitNetwork.check_sound _ _ _ h x.val (Nat.zero_le _) x.isLt
  simpa only [mapCheck, Nat.mod_eq_of_lt x.isLt, decide_eq_true_eq] using hx

def inverseCheck (p q : Nat) (n : Nat) : Bool :=
  let x : Fin 3510 := ⟨n % 3510, Nat.mod_lt _ (by decide)⟩
  decide (packedAction p (packedAction q x) = x)

theorem inverseCheck_sound (p q : Nat)
    (h : BitNetwork.check (inverseCheck p q) 0 3510 = true) :
    ∀ x, packedAction p (packedAction q x) = x := by
  intro x
  have hx := BitNetwork.check_sound _ _ _ h x.val (Nat.zero_le _) x.isLt
  simpa only [inverseCheck, Nat.mod_eq_of_lt x.isLt, decide_eq_true_eq] using hx

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
