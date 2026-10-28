module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Representatives
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.CoreWitness
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables
import Mathlib.Tactic.Tauto

/-!
# The seven max3 interval labels

The eight Schreier words determine membership of every original generator
whenever their closure has relative index two. Schreier's lemma then proves
that every true pivot gives the same subgroup for this mask. This is a proved
consequence of the index hypothesis, rather than an assumption about labels.

A four-point-base calculation identifies the certified core word with a short
word in the four representative generators. Its image in any quotient of order
two is the image of generator 1. Containment of the core word therefore forces
mask bit 1 to be false, leaving the seven nonzero masks below.

Sources: GLS3 Table 5.3p and the literal ATLAS HeG1-p2058B0/max3 words.
The short identity was discovered by GAP factorization and is checked here in
the Lean kernel. All indices are zero-based; original GAP permutations are
inverted by Held's existing model, preserving word order.
-/

public section
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
open Subgroup
open Held.LocalPairs.SylowGeometry.Calculations

/-- Max3 uses the original, unconjugated representative. -/
theorem fixedSubgroup_false : fixedSubgroup false = representative := by
  change representative.map (MonoidHom.id He) = representative
  exact map_id _

/-- Max3 uses each of the four original representative generators. -/
theorem fixedGenerator_false (j : Fin 4) : fixedGenerator false j = generator j := by
  simp [fixedGenerator, fixedConjugator]

private theorem word_mem (i : Bool) (k : Fin 4) (mask : Fin 4 → Bool)
    (e : Bool) (j : Fin 4) :
    indexTwoGenerator (fixedGenerator i) k mask e j ∈ entry i k mask :=
  subset_closure ⟨e, j, rfl⟩

/-- A proper index-two entry recovers its mask as generator nonmembership. -/
theorem generator_mem_iff (i : Bool) (k : Fin 4) (mask : Fin 4 → Bool)
    (hi : (entry i k mask).relIndex (fixedSubgroup i) = 2) (j : Fin 4) :
    fixedGenerator i j ∈ entry i k mask ↔ mask j = false := by
  have ht : fixedGenerator i k ∉ entry i k mask := by
    intro ht
    have hgen (l : Fin 4) : fixedGenerator i l ∈ entry i k mask := by
      have hw := word_mem i k mask false l
      cases hm : mask l
      · simpa [indexTwoGenerator, hm] using hw
      · have hp : fixedGenerator i l * (fixedGenerator i k)⁻¹ ∈ entry i k mask := by
          simpa [indexTwoGenerator, hm] using hw
        simpa using mul_mem hp ht
    have hle : fixedSubgroup i ≤ entry i k mask := by
      rw [← fixedGenerator_closure]
      exact (closure_le _).mpr (by rintro _ ⟨l, rfl⟩; exact hgen l)
    have := relIndex_eq_one.mpr hle
    omega
  have hw := word_mem i k mask false j
  cases hm : mask j
  · simpa [indexTwoGenerator, hm] using hw
  · have hp : fixedGenerator i j * (fixedGenerator i k)⁻¹ ∈ entry i k mask := by
      simpa [indexTwoGenerator, hm] using hw
    simp only [Bool.true_eq_false, iff_false]
    intro hj
    exact ht (inv_mem_iff.mp ((entry i k mask).mul_mem_cancel_left hj |>.mp hp))

/-- Changing to another true pivot preserves a proper index-two entry. -/
theorem entry_eq_of_pivot (i : Bool) (k l : Fin 4) (mask : Fin 4 → Bool)
    (hi : (entry i k mask).relIndex (fixedSubgroup i) = 2)
    (hl : mask l = true) : entry i l mask = entry i k mask := by
  let P := fixedSubgroup i
  let s : Fin 4 → P := fun j => ⟨fixedGenerator i j,
    by
      change fixedGenerator i j ∈ fixedSubgroup i
      rw [← fixedGenerator_closure]
      exact subset_closure (Set.mem_range_self j)⟩
  have hs : closure (Set.range s) = ⊤ := by
    apply map_injective P.subtype_injective
    rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map, range_subtype]
    exact fixedGenerator_closure i
  let H := (entry i k mask).subgroupOf P
  have hmem (j : Fin 4) : s j ∈ H ↔ mask j = false := generator_mem_iff i k mask hi j
  have hout : s l ∉ H := by simp [hmem, hl]
  have hmask (j : Fin 4) : mask j = true ↔ s j ∉ H := by simp [hmem]
  have he := indexTwoClosure_eq s hs H hi l hout mask hmask
  have hm := congrArg (map P.subtype) he
  rw [map_indexTwoClosure, map_subgroupOf_eq_of_le (entry_le_fixedSubgroup i k mask)] at hm
  exact hm

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
/-- A literal identity in the degree-2058 Held carrier. -/
theorem core_word_identity : localWord false ^ 6 =
    (generator 3)⁻¹ * (generator 3)⁻¹ * (generator 3)⁻¹ * (generator 0)⁻¹ *
      generator 1 * generator 0 * generator 1 * (generator 3)⁻¹ * (generator 1)⁻¹ := by
  apply Held.eq_of_four_point_images
  have hl : Held.TwoLocalCandidates.Cores.Tables0.p1 = representation (localWord false) :=
    Held.TwoLocalCandidates.Cores.Tables0.p1_eq
  simp only [map_pow, map_mul, map_inv, ← hl,
    ← TwoGroup.Tables.g0_eq, ← TwoGroup.Tables.g1_eq, ← TwoGroup.Tables.g3_eq]
  decide +kernel

private theorem word_parity {G : Type*} [Group G] (H : Subgroup G)
    (hi : H.index = 2) (x y z : G) :
    z⁻¹ * z⁻¹ * z⁻¹ * x⁻¹ * y * x * y * z⁻¹ * y⁻¹ ∈ H ↔ y ∈ H := by
  simp only [mul_mem_iff_of_index_two hi, inv_mem_iff]
  tauto

/-- The certified core word excludes every mask whose bit 1 is true. -/
theorem mask_one_false (k : Fin 4) (mask : Fin 4 → Bool)
    (hw : localWord false ^ 6 ∈ entry false k mask)
    (hi : (entry false k mask).relIndex (fixedSubgroup false) = 2) :
    mask 1 = false := by
  let P := fixedSubgroup false
  let s : Fin 4 → P := fun j => ⟨fixedGenerator false j,
    by
      change fixedGenerator false j ∈ fixedSubgroup false
      rw [← fixedGenerator_closure]
      exact subset_closure (Set.mem_range_self j)⟩
  let H := (entry false k mask).subgroupOf P
  have hm : (s 3)⁻¹ * (s 3)⁻¹ * (s 3)⁻¹ * (s 0)⁻¹ *
      s 1 * s 0 * s 1 * (s 3)⁻¹ * (s 1)⁻¹ ∈ H := by
    change (fixedGenerator false 3)⁻¹ * (fixedGenerator false 3)⁻¹ *
      (fixedGenerator false 3)⁻¹ * (fixedGenerator false 0)⁻¹ *
      fixedGenerator false 1 * fixedGenerator false 0 * fixedGenerator false 1 *
      (fixedGenerator false 3)⁻¹ * (fixedGenerator false 1)⁻¹ ∈ entry false k mask
    simpa only [fixedGenerator_false, ← core_word_identity] using hw
  have hidx : H.index = 2 := hi
  have h1 : s 1 ∈ H := (word_parity H hidx (s 0) (s 1) (s 3)).mp hm
  exact (generator_mem_iff false k mask hi 1).mp h1

/-- The nonzero mask integers with bit 1 unset. -/
@[expose] def labelNumber : Fin 7 → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 5
  | 3 => 8
  | 4 => 9
  | 5 => 12
  | 6 => 13

/-- The four membership bits of a selected mask. -/
@[expose] def labelMask (t : Fin 7) (j : Fin 4) : Bool :=
  (labelNumber t).testBit j.val

/-- The first true bit, used only to give each selected entry a fixed name. -/
@[expose] def labelPivot : Fin 7 → Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 0
  | 3 => 3
  | 4 => 0
  | 5 => 2
  | 6 => 0

/-- Seven actual word-generated subgroups of Held. No order is asserted here. -/
@[expose] def selectedEntry (t : Fin 7) : Subgroup He :=
  entry false (labelPivot t) (labelMask t)

theorem labelPivot_true (t : Fin 7) : labelMask t (labelPivot t) = true := by
  have h : ∀ t : Fin 7, labelMask t (labelPivot t) = true := by decide +kernel
  exact h t

private theorem mask_exhaustion : ∀ mask : Fin 4 → Bool,
    mask 1 = false → (∃ k, mask k = true) → ∃ t : Fin 7, mask = labelMask t := by
  decide +kernel

/-- Every admissible label, including every pivot choice, is one of the seven
canonical entries. The core witness and relative index are both essential. -/
theorem exists_selected_entry (k : Fin 4) (mask : Fin 4 → Bool)
    (hk : mask k = true) (hw : localWord false ^ 6 ∈ entry false k mask)
    (hi : (entry false k mask).relIndex (fixedSubgroup false) = 2) :
    ∃ t : Fin 7, entry false k mask = selectedEntry t := by
  obtain ⟨t, ht⟩ := mask_exhaustion mask (mask_one_false k mask hw hi) ⟨k, hk⟩
  subst mask
  exact ⟨t, (entry_eq_of_pivot false k (labelPivot t) (labelMask t) hi
    (labelPivot_true t)).symm⟩

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
