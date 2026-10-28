module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.SylowData
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.RadicalOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.Containment
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.FinCases

/-!
# Order and index of the fixed Hall--Janko two-subgroups

Checked generator transitions prove that two explicit cosets of `q₂` cover
`s`. Evaluation at two permutation points distinguishes all 128 elements.
Thus the inclusion already proved in `Containment` has relative index two.
Source: GLS3, Table 5.3g; witnesses from ATLAS J2G1-p100B0.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
open Theory.GroupTheory GeneratorPair Seed RadicalData SylowData
open GeneratorPair.SecondOrbitCertificate

private theorem inclusion_localWord (w : List (Fin 3)) :
    inclusion (localWord w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a, b, b⁻¹] i * localWord w) = _
    rw [map_mul, ih]
    congr 1
    fin_cases i <;> simp [a, b, inclusion, generatorA_eq_table, generatorB_eq_table]

set_option maxRecDepth 100000 in
private theorem sGen_word_check : ∀ i,
    evalWord ![tableA, tableB, tableB⁻¹] (sWords i) = sGenTable i := by
  apply allFin
  decide +kernel

theorem sGenerator_inclusion (i : Fin 7) : inclusion (sGenerator i) = sGenTable i :=
  (inclusion_localWord (sWords i)).trans (sGen_word_check i)

set_option maxRecDepth 100000 in
private theorem t_check : sGenTable 3 = tTable := by decide +kernel

set_option maxRecDepth 100000 in
private theorem sTable_step_check : ∀ j i,
    sGenTable j * sTable i = sTable (sStep j i) := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem sTable_invStep_check : ∀ j i,
    (sGenTable j)⁻¹ * sTable i = sTable (sInvStep j i) := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem sKey_decode : ∀ i, sDecode (sKey i) = i := by
  apply allFin
  decide +kernel

/-- Two explicit cosets of the radical, in the original carrier. -/
def sElement (i : Fin 128) : Carrier :=
  if i.val < 64 then qElement ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  else sGenerator 3 * qElement ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

theorem sElement_inclusion (i : Fin 128) : inclusion (sElement i) = sTable i := by
  unfold sElement sTable
  split
  · exact qElement_inclusion _
  · rw [map_mul, sGenerator_inclusion, t_check, qElement_inclusion]

theorem sElement_mem (i : Fin 128) : sElement i ∈ s := by
  unfold sElement
  split
  · exact q₂_le_s (qElement_mem _)
  · exact s.mul_mem (Subgroup.subset_closure ⟨3, rfl⟩) (q₂_le_s (qElement_mem _))

/-- Generator transitions give exhaustive coverage of the unchanged Seed. -/
theorem exists_sElement {x : Carrier} (hx : x ∈ s) : ∃ i, sElement i = x := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, rfl⟩
  | mul_left x hx y hy ih =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := ih
    refine ⟨sStep j i, inclusion_injective ?_⟩
    rw [map_mul, sElement_inclusion, sElement_inclusion, sGenerator_inclusion]
    exact (sTable_step_check j i).symm
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := ih
    refine ⟨sInvStep j i, inclusion_injective ?_⟩
    rw [map_mul, map_inv, sElement_inclusion, sElement_inclusion, sGenerator_inclusion]
    exact (sTable_invStep_check j i).symm

theorem sElement_injective : Function.Injective sElement := by
  intro i j hij
  have h := congrArg inclusion hij
  rw [sElement_inclusion, sElement_inclusion] at h
  have hk : sKey i = sKey j :=
    congrArg (fun p : Equiv.Perm (Fin 100) => 100 * (p 0).val + (p 1).val) h
  exact (sKey_decode i).symm.trans ((congrArg sDecode hk).trans (sKey_decode j))

noncomputable def sEquivFin : s ≃ Fin 128 :=
  (Equiv.ofBijective (fun i => (⟨sElement i, sElement_mem i⟩ : s))
    ⟨fun _ _ h => sElement_injective (congrArg Subtype.val h),
      fun x => by
        obtain ⟨i, hi⟩ := exists_sElement x.property
        exact ⟨i, Subtype.ext hi⟩⟩).symm

theorem card_s : Nat.card s = 128 := by
  simpa using Nat.card_congr sEquivFin

theorem q₂_relIndex_s : q₂.relIndex s = 2 := by
  have hc : Nat.card (q₂.subgroupOf s) = 64 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe q₂_le_s).toEquiv).trans card_q₂
  have h := (q₂.subgroupOf s).card_mul_index
  rw [hc, card_s] at h
  change (q₂.subgroupOf s).index = 2
  omega

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
