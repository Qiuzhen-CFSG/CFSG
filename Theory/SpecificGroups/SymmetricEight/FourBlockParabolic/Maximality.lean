module
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
# Maximality of the even four-block stabilizer

The stabilizer in A₈ of {0,1,2,3} has index 70, by transitivity on four-element
subsets. The even permutation (04)(15)(26)(37) exchanges the two blocks, so
that stabilizer has index two in the unordered partition stabilizer. The
latter therefore has index 35. A proper larger subgroup would have index 5
or 7. Simplicity makes its coset action faithful, contradicting |A₈| = 20160.

This establishes maximality inside A₈ directly. Source: Aschbacher–Smith,
*The Classification of Quasithin Groups*, 15.3.32(4), printed pp.1132–1133.
-/

open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Subgroup
namespace Theory.SpecificGroups.SymmetricEight.FourBlockParabolic
private abbrev Alt := alternatingGroup (Fin 8)
private def evenFour : Subgroup Alt := fourStabilizer.subgroupOf Alt
private instance (a : Alt) : Decidable (a ∈ evenFour) :=
  inferInstanceAs (Decidable (a.val ∈ fourStabilizer))

private def half : Set.powersetCard (Fin 8) 4 :=
  ⟨{0,1,2,3}, by change ({0,1,2,3} : Finset (Fin 8)).card = 4; decide⟩
private def halfStabilizer : Subgroup Alt := MulAction.stabilizer Alt half

private theorem half_mem (i : Fin 8) : i ∈ (half : Set (Fin 8)) ↔ i.val / 4 = 0 := by
  change i ∈ ({0,1,2,3} : Finset (Fin 8)) ↔ i.val / 4 = 0
  fin_cases i <;> decide

set_option backward.isDefEq.respectTransparency false in
private theorem mem_half (p : Alt) : p ∈ halfStabilizer ↔
    ∀ i : Fin 8, (p.val i).val / 4 = 0 ↔ i.val / 4 = 0 := by
  rw [halfStabilizer]
  rw [Set.powersetCard.stabilizer_coe (G := Alt) half, MulAction.mem_stabilizer_set]
  change (∀ i : Fin 8, p.val i ∈ (half : Set (Fin 8)) ↔ i ∈ (half : Set (Fin 8))) ↔ _
  simp only [half_mem]

private theorem half_le_even : halfStabilizer ≤ evenFour := by
  intro p hp
  have h := (mem_half p).mp hp
  change p.val ∈ fourStabilizer
  intro i j
  have ht : ∀ a b c d : Fin 8,
      (a.val / 4 = 0 ↔ b.val / 4 = 0) → (c.val / 4 = 0 ↔ d.val / 4 = 0) →
      (a.val / 4 = c.val / 4 ↔ b.val / 4 = d.val / 4) := by decide +kernel
  exact ht _ _ _ _ (h i) (h j)

private theorem mem_half_of_even (p : Alt) (hp : p ∈ evenFour) :
    p ∈ halfStabilizer ↔ (p.val 0).val / 4 = 0 := by
  rw [mem_half]
  constructor
  · exact fun h => (h 0).mpr rfl
  · intro h i
    have hh := hp i 0
    change (p.val i).val / 4 = (p.val 0).val / 4 ↔ i.val / 4 = 0 at hh
    rwa [h] at hh

private def flip : Alt :=
  ⟨Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7, by
    change Equiv.Perm.sign _ = 1
    decide⟩

private theorem flip_mem : flip ∈ evenFour := by decide

private theorem half_rel_index : halfStabilizer.relIndex evenFour = 2 := by
  apply (index_eq_two_iff' (H := halfStabilizer.subgroupOf evenFour)).mpr
  refine ⟨⟨flip, flip_mem⟩, fun b => ?_⟩
  change Xor (flip * b.val ∈ halfStabilizer) (b.val ∈ halfStabilizer)
  rw [mem_half_of_even _ (evenFour.mul_mem flip_mem b.property),
    mem_half_of_even _ b.property]
  change Xor ((flip.val (b.val.val 0)).val / 4 = 0) ((b.val.val 0).val / 4 = 0)
  have ht : ∀ i : Fin 8, Xor ((flip.val i).val / 4 = 0) (i.val / 4 = 0) := by decide
  exact ht _

private theorem half_index : halfStabilizer.index = 70 := by
  have : MulAction.IsPretransitive Alt (Set.powersetCard (Fin 8) 4) :=
    Set.powersetCard.isPretransitive_alternatingGroup (by simp)
  rw [halfStabilizer, MulAction.index_stabilizer_of_transitive, Set.powersetCard.card]
  norm_num [Nat.choose]

private theorem alt_card : Nat.card Alt = 20160 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at h ⊢
  omega

private theorem evenFour_index : evenFour.index = 35 := by
  have h := halfStabilizer.relIndex_mul_index half_le_even
  rw [half_rel_index, half_index] at h
  omega

/-- The even four-block subgroup is maximal in the alternating group. -/
public theorem fourStabilizer_subgroupOf_isCoatom :
    IsCoatom (fourStabilizer.subgroupOf (alternatingGroup (Fin 8))) := by
  change IsCoatom evenFour
  refine ⟨?_, ?_⟩
  · intro h
    have hi := evenFour_index
    simp [h] at hi
  · intro K hK
    by_contra hKt
    have hcore : K.normalCore = ⊥ := by
      rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 8) (by simp)
        (N := K.normalCore) with h | h
      · exact h
      · exact (hKt (top_unique (h ▸ K.normalCore_le))).elim
    have hd : Nat.card Alt ∣ K.index.factorial := by
      have hh : K.normalCore.index ∣ K.index.factorial := by
        rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
        exact card_subgroup_dvd_card (MulAction.toPermHom Alt (Alt ⧸ K)).range
      simpa [hcore] using hh
    have hdiv : K.index ∣ 35 := evenFour_index ▸ index_dvd_of_le hK.le
    have hlt : K.index < 35 := evenFour_index ▸ index_strictAnti hK
    have hne : K.index ≠ 1 := fun h => hKt (index_eq_one.mp h)
    have hi : K.index = 5 ∨ K.index = 7 := by
      have ht : ∀ n : Fin 35, (n.val ∣ 35) → n.val ≠ 1 → n.val = 5 ∨ n.val = 7 := by decide
      exact ht ⟨K.index, hlt⟩ hdiv hne
    rw [alt_card] at hd
    rcases hi with h | h <;> rw [h] at hd <;> norm_num [Nat.factorial] at hd
end Theory.SpecificGroups.SymmetricEight.FourBlockParabolic
