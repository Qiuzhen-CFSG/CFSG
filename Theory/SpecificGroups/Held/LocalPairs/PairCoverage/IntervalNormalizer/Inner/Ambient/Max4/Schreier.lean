module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Data

/-!
# Exhaustion of max4 entries by seven masks

In a proper index-two Schreier closure the pivot cannot belong to the closure:
otherwise every original generator belongs. Hence the mask recovers exactly
which generators are outside, and Schreier's lemma identifies every alternative
true pivot with the same subgroup. This uses the index hypothesis explicitly.

A four-point-base certificate identifies the fifth power of the max4 word with
an eight-letter word in the aligned generators. In the index-two quotient its
parity is the sum of coordinates two and three. The core-word membership
hypothesis therefore forces those two mask bits to agree, leaving seven masks.

Sources: Schreier's lemma; the unchanged ATLAS HeG1-p2058B0 carrier and max4
program. The discovery word is retained in `Source/README.md`; all used equality
and finite-exhaustion assertions below are checked by Lean's kernel.
-/

public section
open Subgroup
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient

theorem word_mem (k : Fin 4) (mask : Fin 4 → Bool) (e : Bool) (j : Fin 4) :
    indexTwoGenerator (fixedGenerator true) k mask e j ∈ entry true k mask :=
  subset_closure ⟨e, j, rfl⟩

private theorem pivot_not_mem (k : Fin 4) (mask : Fin 4 → Bool)
    (hi : (entry true k mask).relIndex (fixedSubgroup true) = 2) :
    fixedGenerator true k ∉ entry true k mask := by
  intro hk
  have hle : fixedSubgroup true ≤ entry true k mask := by
    rw [← fixedGenerator_closure]
    apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    have hw := word_mem k mask false j
    cases hm : mask j
    · simpa [indexTwoGenerator, hm] using hw
    · have hh := mul_mem hw hk
      simpa [indexTwoGenerator, hm] using hh
  have he := le_antisymm (entry_le_fixedSubgroup true k mask) hle
  simp [he] at hi

theorem generator_mem_iff (k : Fin 4) (mask : Fin 4 → Bool)
    (hi : (entry true k mask).relIndex (fixedSubgroup true) = 2) (j : Fin 4) :
    fixedGenerator true j ∈ entry true k mask ↔ mask j = false := by
  have hw := word_mem k mask false j
  cases hm : mask j
  · simp only [iff_true]
    simpa [indexTwoGenerator, hm] using hw
  · simp only [Bool.true_eq_false, iff_false]
    intro hj
    have hh := (entry true k mask).mul_mem_cancel_left hj |>.mp
      (show fixedGenerator true j * (fixedGenerator true k)⁻¹ ∈ entry true k mask by
        simpa [indexTwoGenerator, hm] using hw)
    exact pivot_not_mem k mask hi ((entry true k mask).inv_mem_iff.mp hh)

theorem entry_change_pivot (k l : Fin 4) (mask : Fin 4 → Bool)
    (hl : mask l = true)
    (hi : (entry true k mask).relIndex (fixedSubgroup true) = 2) :
    entry true l mask = entry true k mask := by
  let P := fixedSubgroup true
  let E := entry true k mask
  let t : Fin 4 → P := fun j => ⟨fixedGenerator true j,
    show fixedGenerator true j ∈ fixedSubgroup true from
      fixedGenerator_closure true ▸ subset_closure (Set.mem_range_self j)⟩
  have ht : closure (Set.range t) = ⊤ := by
    apply map_injective P.subtype_injective
    rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map, range_subtype]
    exact fixedGenerator_closure true
  have hmask (j : Fin 4) : mask j = true ↔ t j ∉ E.subgroupOf P := by
    change mask j = true ↔ fixedGenerator true j ∉ entry true k mask
    rw [generator_mem_iff k mask hi j]
    cases mask j <;> simp
  have he := indexTwoClosure_eq t ht (E.subgroupOf P) hi l ((hmask l).mp hl) mask hmask
  have hm := congrArg (map P.subtype) he
  rw [map_indexTwoClosure, map_subgroupOf_eq_of_le (entry_le_fixedSubgroup true k mask)] at hm
  exact hm
private def coreWord : He :=
  (fixedGenerator true 2)⁻¹ * (fixedGenerator true 3)⁻¹ *
    (fixedGenerator true 3)⁻¹ * (fixedGenerator true 0)⁻¹ *
    (fixedGenerator true 1)⁻¹ * (fixedGenerator true 3)⁻¹ *
    (fixedGenerator true 1)⁻¹ * (fixedGenerator true 0)⁻¹

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem coreWord_eq : localWord true ^ 5 = coreWord := by
  apply Held.eq_of_four_point_images
  decide +kernel

theorem mask_constraint (k : Fin 4) (mask : Fin 4 → Bool)
    (hi : (entry true k mask).relIndex (fixedSubgroup true) = 2)
    (hc : localWord true ^ 5 ∈ entry true k mask) : mask 2 = mask 3 := by
  let P := fixedSubgroup true
  let E := (entry true k mask).subgroupOf P
  let t : Fin 4 → P := fun j => ⟨fixedGenerator true j,
    show fixedGenerator true j ∈ fixedSubgroup true from
      fixedGenerator_closure true ▸ subset_closure (Set.mem_range_self j)⟩
  have hmem (j : Fin 4) : t j ∈ E ↔ mask j = false := generator_mem_iff k mask hi j
  have hh : (t 2)⁻¹ * (t 3)⁻¹ * (t 3)⁻¹ * (t 0)⁻¹ *
      (t 1)⁻¹ * (t 3)⁻¹ * (t 1)⁻¹ * (t 0)⁻¹ ∈ E := by
    change coreWord ∈ entry true k mask
    rwa [← coreWord_eq]
  simp only [E.mul_mem_iff_of_index_two hi, E.inv_mem_iff, hmem] at hh
  cases h0 : mask 0 <;> cases h1 : mask 1 <;>
    cases h2 : mask 2 <;> cases h3 : mask 3 <;> simp_all

/-- Each chosen canonical pivot is outside according to its mask. -/
theorem pivot_true (j : Fin 7) : mask j (pivot j) = true := by
  fin_cases j <;> decide

private theorem mask_complete : ∀ (k : Fin 4) (m : Fin 4 → Bool),
    m k = true → m 2 = m 3 → ∃ j : Fin 7, mask j = m := by
  decide +kernel

/-- All original labels, including nonminimal pivots, reduce to these seven
actual subgroups. No equality of distinct masks is asserted. -/
theorem exists_candidate (k : Fin 4) (m : Fin 4 → Bool) (hk : m k = true)
    (hi : (entry true k m).relIndex (fixedSubgroup true) = 2)
    (hc : localWord true ^ 5 ∈ entry true k m) :
    ∃ j : Fin 7, candidate j = entry true k m := by
  obtain ⟨j, hj⟩ := mask_complete k m hk (mask_constraint k m hi hc)
  refine ⟨j, ?_⟩
  unfold candidate
  rw [hj]
  exact entry_change_pivot k (pivot j) m (hj ▸ pivot_true j) hi

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
