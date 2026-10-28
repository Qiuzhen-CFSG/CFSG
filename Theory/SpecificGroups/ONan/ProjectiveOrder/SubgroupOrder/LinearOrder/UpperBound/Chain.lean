module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearSetup
public import Theory.GroupTheory.WordSubgroup.FiniteCover
public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearOrder.UpperBound.NextWords
import Mathlib.Tactic.FinCases

/-!
# The concrete word chain for the linear O'Nan local subgroup

The five proposed indices are 2793, 56, 6, 2, 2. This module fixes the exact
signed generators at all six levels, proves the subgroup inclusions, identifies
the first subgroup with the specified linear local subgroup, and proves that
the last subgroup is trivial. No index or transition claim is assumed here.

Positive generators are followed by their inverses. Words are obtained from
`source/chain-witness.json`; the original generators and their attribution are
in `refs/original/onan/` and `ProjectiveOrder/source/`.
-/

namespace ONan.OrderCertificate.LinearUpperBound

open Theory.GroupTheory

public abbrev G := Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)

/-- Append the inverses to a family of positive generators. -/
@[expose] public def signed {n : Nat} (g : Fin n → G) : Fin (n+n) → G :=
  Fin.addCases g (fun i => (g i)⁻¹)

/-- Interchange the positive and negative halves of the alphabet. -/
@[expose] public def invIndex (n : Nat) : Fin (n+n) → Fin (n+n) :=
  Fin.addCases (Fin.natAdd n) (Fin.castAdd n)

public theorem signed_inv {n : Nat} (g : Fin n → G) (i : Fin (n+n)) :
    signed g (invIndex n i) = (signed g i)⁻¹ := by
  cases i using Fin.addCases <;>
    simp only [signed, invIndex, Fin.addCases_left, Fin.addCases_right, inv_inv]

/-- Decode a table word. Out-of-range letters are discarded; all supplied
letters are in range. Soundness of the cover does not require a separate
well-formedness hypothesis on the raw data. -/
@[expose] public def decodeWord (n : Nat) (w : List Nat) : List (Fin n) :=
  w.filterMap fun i => if h : i < n then some ⟨i, h⟩ else none

public theorem signed_mem {n : Nat} (g : Fin n → G) (H : Subgroup G)
    (h : ∀ i, g i ∈ H) (i : Fin (n+n)) : signed g i ∈ H := by
  cases i using Fin.addCases with
  | left i => simpa only [signed, Fin.addCases_left] using h i
  | right i => simpa only [signed, Fin.addCases_right] using H.inv_mem (h i)

public theorem word_mem {n : Nat} (g : Fin n → G) (H : Subgroup G)
    (h : ∀ i, g i ∈ H) (w : List (Fin n)) : evalWord g w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (h i) ih

@[expose] public def positive0 : Fin 2 → G := ![linearLocalA, linearLocalB]
@[expose] public def gen0 : Fin 4 → G := signed positive0
@[expose] public def group0 : Subgroup G := wordSubgroup gen0 (invIndex 2) (signed_inv positive0)

public theorem group0_eq : group0 = linearLocalSubgroup := by
  apply le_antisymm
  · intro g hg
    obtain ⟨w, rfl⟩ := hg
    apply word_mem gen0 linearLocalSubgroup _ w
    apply signed_mem positive0 linearLocalSubgroup
    intro i
    fin_cases i
    · exact linearLocalA_mem
    · exact linearLocalB_mem
  · apply (Subgroup.closure_le group0).2
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨[0], mul_one _⟩
    · exact ⟨[1], mul_one _⟩

@[expose] public def positive1 (i : Fin 3) : G :=
  evalWord gen0 (decodeWord 4 (nextWords0.getD i.val []))
@[expose] public def gen1 : Fin 6 → G := signed positive1
@[expose] public def group1 : Subgroup G :=
  wordSubgroup gen1 (invIndex 3) (signed_inv positive1)

public theorem group1_le : group1 ≤ group0 := by
  apply wordSubgroup_le_of_gen_mem
  apply signed_mem positive1 group0
  intro i
  exact ⟨_, rfl⟩

@[expose] public def positive2 (i : Fin 4) : G :=
  evalWord gen1 (decodeWord 6 (nextWords1.getD i.val []))
@[expose] public def gen2 : Fin 8 → G := signed positive2
@[expose] public def group2 : Subgroup G :=
  wordSubgroup gen2 (invIndex 4) (signed_inv positive2)

public theorem group2_le : group2 ≤ group1 := by
  apply wordSubgroup_le_of_gen_mem
  apply signed_mem positive2 group1
  intro i
  exact ⟨_, rfl⟩

@[expose] public def positive3 (i : Fin 2) : G :=
  evalWord gen2 (decodeWord 8 (nextWords2.getD i.val []))
@[expose] public def gen3 : Fin 4 → G := signed positive3
@[expose] public def group3 : Subgroup G :=
  wordSubgroup gen3 (invIndex 2) (signed_inv positive3)

public theorem group3_le : group3 ≤ group2 := by
  apply wordSubgroup_le_of_gen_mem
  apply signed_mem positive3 group2
  intro i
  exact ⟨_, rfl⟩

@[expose] public def positive4 (i : Fin 1) : G :=
  evalWord gen3 (decodeWord 4 (nextWords3.getD i.val []))
@[expose] public def gen4 : Fin 2 → G := signed positive4
@[expose] public def group4 : Subgroup G :=
  wordSubgroup gen4 (invIndex 1) (signed_inv positive4)

public theorem group4_le : group4 ≤ group3 := by
  apply wordSubgroup_le_of_gen_mem
  apply signed_mem positive4 group3
  intro i
  exact ⟨_, rfl⟩

@[expose] public def positive5 (i : Fin 0) : G :=
  evalWord gen4 (decodeWord 2 (nextWords4.getD i.val []))
@[expose] public def gen5 : Fin 0 → G := signed positive5
@[expose] public def group5 : Subgroup G :=
  wordSubgroup gen5 (invIndex 0) (signed_inv positive5)

public theorem group5_le : group5 ≤ group4 := by
  apply wordSubgroup_le_of_gen_mem
  apply signed_mem positive5 group4
  intro i
  exact ⟨_, rfl⟩

public theorem group5_card : Nat.card group5 = 1 :=
  wordSubgroup_fin_zero_card gen5 (invIndex 0) (signed_inv positive5)

end ONan.OrderCertificate.LinearUpperBound
