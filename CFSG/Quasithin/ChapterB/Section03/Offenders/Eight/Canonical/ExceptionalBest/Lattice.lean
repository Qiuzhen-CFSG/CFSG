module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.ExceptionalBest.Words
import Mathlib.Data.Finset.Max
/-!
# Exhaustive subgroup model for the exceptional group

Each word subspace gives a concrete subgroup, with its order equal to the
number of words. A maximal contained table cannot omit a word of a given
subgroup: adjoining that word produces a larger contained table. Thus every
subgroup of the exceptional group occurs in the 67-entry list.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(2),(5),(6), printed pp. 83–84.
-/

@[expose] public section
open BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Offenders.Eight.ExceptionalBest

def perms (i : Fin 67) : Finset Perm := (words i).image exceptionalWords

def group (i : Fin 67) : Subgroup Perm where
  carrier := (perms i : Set Perm)
  one_mem' := Finset.mem_image.mpr ⟨0, (words_closed i).1, rfl⟩
  mul_mem' := by
    rintro a b ha hb
    change a ∈ (words i).image exceptionalWords at ha
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.mp ha
    change b ∈ (words i).image exceptionalWords at hb
    obtain ⟨b, hb', rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨xor a b, (words_closed i).2 a ha' b hb', word_mul a b⟩
  inv_mem' := by
    rintro a ha
    change a ∈ (words i).image exceptionalWords at ha
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨a, ha', (word_inv a).symm⟩

theorem closure_perms (i : Fin 67) : Subgroup.closure (perms i : Set Perm) = group i :=
  Subgroup.closure_eq (group i)

theorem card_group (i : Fin 67) : Nat.card (group i) = (words i).card := by
  change Nat.card ↥(perms i) = _
  rw [Nat.card_eq_finsetCard, perms,
    Finset.card_image_of_injective _ word_injective]

/-- Exhaustiveness follows by maximizing a contained table and adjoining any missing word. -/
theorem subgroup_eq_group (B : Subgroup Perm) (hB : B ≤ exceptional 8 (by decide)) :
    ∃ i, B = group i := by
  classical
  let S := Finset.univ.filter (fun i => group i ≤ B)
  have hzero : (0 : Fin 67) ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro g hg
    change g ∈ (words 0).image exceptionalWords at hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hg
    have ha0 : a = 0 := by simpa [words] using ha
    subst a
    exact B.one_mem
  obtain ⟨i, hi, hmax⟩ := S.exists_max_image (fun i => (words i).card) ⟨0, hzero⟩
  have hiB : group i ≤ B := (Finset.mem_filter.mp hi).2
  refine ⟨i, le_antisymm ?_ hiB⟩
  intro g hg
  obtain ⟨j, rfl⟩ := (mem_exceptional_iff g).mp (hB hg)
  obtain ⟨k, hik, hjk, hk⟩ := words_extend i j
  have hkB : group k ≤ B := by
    intro x hx
    change x ∈ (words k).image exceptionalWords at hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
    rcases hk l hl with hl | ⟨a, ha, rfl⟩
    · exact hiB (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    · rw [word_mul]
      exact B.mul_mem hg (hiB (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
  have he : words i = words k := Finset.eq_of_subset_of_card_le hik
    (hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkB⟩))
  exact Finset.mem_image.mpr ⟨j, he.symm ▸ hjk, rfl⟩

end CFSG.Quasithin.ChapterB.Offenders.Eight.ExceptionalBest
