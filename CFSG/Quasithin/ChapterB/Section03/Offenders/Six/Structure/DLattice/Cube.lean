module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Representatives
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Basic
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Reduction
import Mathlib.Tactic.FinCases

/-!
# The subgroup lattice of three disjoint transpositions

The eight words in the three transpositions identify `D` with a binary cube.
We enumerate its sixteen subgroups, including the trivial subgroup, by their
word indices. Closure and exhaustiveness are finite certificates on this cube.
The seven planes are then characterized by the actual lattice cover relation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2 and Lemma B.3.4, printed pp. 83–85.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Six
open Representation.BinaryOffender

/-- Word indices of all subgroups of `D`: the trivial group, seven lines,
three coordinate planes, three mixed planes, the even plane, and `D`. -/
def dLatticeIndices : Fin 16 → Finset (Fin 8) :=
  ![{0}, {0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {0,6}, {0,7},
    {0,1,2,3}, {0,1,4,5}, {0,2,4,6},
    {0,1,6,7}, {0,2,5,7}, {0,3,4,7}, {0,3,5,6}, Finset.univ]

theorem dWords_injective : Function.Injective dWords := by decide

/-- The explicit sixteen-entry subgroup list of the binary cube. -/
def dLattice (r : Fin 16) : Subgroup Perm where
  carrier := {g | ∃ i ∈ dLatticeIndices r, dWords i = g}
  one_mem' := ⟨0, by revert r; decide, rfl⟩
  mul_mem' := by
    rintro a b ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    have hc : ∀ r : Fin 16, ∀ i ∈ dLatticeIndices r, ∀ j ∈ dLatticeIndices r,
        ∃ k ∈ dLatticeIndices r, dWords k = dWords i * dWords j := by decide
    exact hc r i hi j hj
  inv_mem' := by
    rintro a ⟨i, hi, rfl⟩
    have hs : ∀ i, dWords i = (dWords i)⁻¹ := by decide
    exact ⟨i, hi, hs i⟩

/-- Membership in the explicit subgroup list. -/
theorem mem_dLattice_iff (r : Fin 16) (g : Perm) :
    g ∈ dLattice r ↔ ∃ i ∈ dLatticeIndices r, dWords i = g := Iff.rfl

@[simp] theorem dWords_mem_dLattice (r : Fin 16) (i : Fin 8) :
    dWords i ∈ dLattice r ↔ i ∈ dLatticeIndices r := by
  simp only [mem_dLattice_iff, dWords_injective.eq_iff, exists_eq_right]

theorem dLattice_le_D (r : Fin 16) : dLattice r ≤ D 6 := by
  rintro g ⟨i, _, rfl⟩
  exact (mem_disjointTranspositions_iff (3 : Fin 4) _).2 ⟨i, rfl⟩

/-- Inclusion in the list is exactly inclusion of word-index sets. -/
theorem dLattice_le_iff (r s : Fin 16) :
    dLattice r ≤ dLattice s ↔ dLatticeIndices r ⊆ dLatticeIndices s := by
  constructor
  · intro h i hi
    exact (dWords_mem_dLattice s i).1 (h ((dWords_mem_dLattice r i).2 hi))
  · rintro h g ⟨i, hi, rfl⟩
    exact (dWords_mem_dLattice s i).2 (h hi)

/-- Distinct entries denote distinct subgroups. -/
theorem dLattice_injective : Function.Injective dLattice := by
  intro r s h
  have he : dLatticeIndices r = dLatticeIndices s := by
    apply Finset.Subset.antisymm
    · exact (dLattice_le_iff r s).1 h.le
    · exact (dLattice_le_iff s r).1 h.ge
  exact (show Function.Injective dLatticeIndices from (by decide)) he

@[simp] theorem dLattice_zero : dLattice 0 = ⊥ := by
  ext g
  simp [mem_dLattice_iff, dLatticeIndices, dWords, cubeWords, eq_comm]

@[simp] theorem dLattice_fifteen : dLattice 15 = D 6 := by
  ext g
  change _ ↔ g ∈ disjointTranspositions 6 (3 : Fin 4).val
  rw [mem_dLattice_iff, mem_disjointTranspositions_iff (3 : Fin 4)]
  simp [dLatticeIndices, initialWords]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Exhaustiveness is checked on the 256 subsets of the eight-word cube. -/
theorem subgroup_le_D_iff (A : Subgroup Perm) :
    A ≤ D 6 ↔ ∃ r : Fin 16, A = dLattice r := by
  classical
  constructor
  · intro hA
    let s : Finset (Fin 8) := Finset.univ.filter fun i => dWords i ∈ A
    have hs0 : (0 : Fin 8) ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, A.one_mem⟩
    have hmul : ∀ i ∈ s, ∀ j ∈ s, ∀ k, dWords k = dWords i * dWords j → k ∈ s := by
      intro i hi j hj k hk
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at *
      rw [hk]
      exact A.mul_mem hi hj
    have certificate : ∀ s : Finset (Fin 8), 0 ∈ s →
        (∀ i ∈ s, ∀ j ∈ s, ∀ k, dWords k = dWords i * dWords j → k ∈ s) →
        ∃ r, s = dLatticeIndices r := by decide
    obtain ⟨r, hr⟩ := certificate s hs0 hmul
    refine ⟨r, ?_⟩
    ext g
    constructor
    · intro hg
      obtain ⟨i, rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) g).1 (hA hg)
      change dWords i ∈ A at hg
      apply (dWords_mem_dLattice r i).2
      rw [← hr]
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hg
    · rintro ⟨i, hi, rfl⟩
      rw [← hr] at hi
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · rintro ⟨r, rfl⟩
    exact dLattice_le_D r

/-- The fifteen nontrivial subgroups of `D`, without duplicates. -/
theorem nontrivial_subgroup_le_D_iff (A : Subgroup Perm) :
    A ≤ D 6 ∧ A ≠ ⊥ ↔ ∃ r : Fin 16, r ≠ 0 ∧ A = dLattice r := by
  rw [subgroup_le_D_iff]
  constructor
  · rintro ⟨⟨r, rfl⟩, h⟩
    exact ⟨r, fun hr => h (hr ▸ dLattice_zero), rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, rfl⟩, fun h => hr (dLattice_injective (h.trans dLattice_zero.symm))⟩

/-- Cardinalities of all entries in the list. -/
theorem card_dLattice (r : Fin 16) : Nat.card (dLattice r) = (dLatticeIndices r).card := by
  classical
  let f : {i // i ∈ dLatticeIndices r} → dLattice r := fun i =>
    ⟨dWords i.val, (dWords_mem_dLattice r i.val).2 i.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact Subtype.ext (dWords_injective (congrArg Subtype.val h))
    · rintro ⟨g, i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

/-- The seven hyperplanes are entries 8 through 14 of the subgroup list. -/
theorem dLattice_covBy_D_iff (r : Fin 16) :
    dLattice r ⋖ D 6 ↔ 8 ≤ r.val ∧ r.val < 15 := by
  rw [← dLattice_fifteen, covBy_iff_lt_and_eq_or_eq]
  have he (r s : Fin 16) : dLattice r = dLattice s ↔ r = s := dLattice_injective.eq_iff
  constructor
  · rintro ⟨hlt, h⟩
    have hne : r ≠ 15 := fun hr => hlt.ne (congrArg dLattice hr)
    have hc : ∀ s : Fin 16, dLatticeIndices r ⊆ dLatticeIndices s → s = r ∨ s = 15 := by
      intro s hs
      exact (h (dLattice s) ((dLattice_le_iff r s).2 hs)
        (by rw [dLattice_fifteen]; exact dLattice_le_D s)).imp (he s r).1 (he s 15).1
    have cert : ∀ r : Fin 16, r ≠ 15 →
        (∀ s : Fin 16, dLatticeIndices r ⊆ dLatticeIndices s → s = r ∨ s = 15) →
        8 ≤ r.val ∧ r.val < 15 := by decide
    exact cert r hne hc
  · intro hr
    refine ⟨lt_of_le_of_ne ?_ ?_, ?_⟩
    · rw [dLattice_fifteen]
      exact dLattice_le_D r
    · intro h
      have := (he r 15).1 h
      subst r
      omega
    · intro A hrA hAD
      rw [dLattice_fifteen] at hAD
      obtain ⟨s, rfl⟩ := (subgroup_le_D_iff A).1 hAD
      have hs := (dLattice_le_iff r s).1 hrA
      have cert : ∀ r s : Fin 16, 8 ≤ r.val ∧ r.val < 15 →
          dLatticeIndices r ⊆ dLatticeIndices s → s = r ∨ s = 15 := by decide
      exact (cert r s hr hs).imp (congrArg dLattice) (congrArg dLattice)

/-- An exhaustive characterization using the actual subgroup cover relation. -/
theorem covBy_D_iff (A : Subgroup Perm) :
    A ⋖ D 6 ↔ ∃ r : Fin 16, 8 ≤ r.val ∧ r.val < 15 ∧ A = dLattice r := by
  constructor
  · intro h
    obtain ⟨r, rfl⟩ := (subgroup_le_D_iff A).1 h.le
    exact ⟨r, (dLattice_covBy_D_iff r).1 h |>.1,
      (dLattice_covBy_D_iff r).1 h |>.2, rfl⟩
  · rintro ⟨r, h1, h2, rfl⟩
    exact (dLattice_covBy_D_iff r).2 ⟨h1, h2⟩

end CFSG.Quasithin.ChapterB.Offenders.Six
