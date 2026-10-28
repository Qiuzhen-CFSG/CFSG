module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Theory.GroupTheory.IndexTwoGenerators
import Mathlib.Tactic.FinCases

/-!
# Fixed subgroups and Schreier words for the Held ambient calculation

We reuse the published four-generator subgroup and the published max4
conjugator. Their images lie in the literal max3 and max4 overgroups.
The max4 membership identities are checked on Held's certified four-point
base, using the same witnesses as TwoLocalCandidates.SylowContainment.

The interval entries are closures of eight Schreier words. Every proper
subgroup of relative index at most two in a fixed subgroup occurs in this
finite family. Their normalizers and the Sylow status of the fixed subgroups
are separate obligations, not consequences of these definitions.

Sources: GLS3 Table 5.3p; ATLAS HeG1-p2058B0 and max3/max4;
TwoLocalCandidates/SylowContainment/source and the cited existing word modules.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient
open Subgroup
open Held.LocalPairs.SylowGeometry.Calculations
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue (conjugator)

private def evalPair (x y : He) (w : List ℤ) : He :=
  (w.map (fun k => if k.natAbs = 1 then x ^ k else
    y ^ (if k < 0 then (-1 : ℤ) else 1))).prod

private theorem evalPair_mem (H : Subgroup He) (x y : He)
    (hx : x ∈ H) (hy : y ∈ H) (w : List ℤ) : evalPair x y w ∈ H := by
  apply H.list_prod_mem
  intro z hz
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hz
  split
  · exact H.zpow_mem hx _
  · exact H.zpow_mem hy _

private theorem map_representative_le (g : He) (H : Subgroup He)
    (h : ∀ j, (MulAut.conj g) (generator j) ∈ H) :
    representative.map (MulAut.conj g).toMonoidHom ≤ H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  change Subgroup.closure (Set.range generator) ≤ _
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact h j

private def max4Words : Fin 4 → List ℤ
  | 0 => [1, -2, 1, 2, 1, 2, 2, 1, -2, -2, 1, -2, 1, 2, 1]
  | 1 => [-2, -2, -2, 1, 2, 1, 2, 2, 1, 2, 1, -2, -2, 1, 2, 2, 1, 2]
  | 2 => [-2, 1, -2, 1, 2, 1, 2]
  | 3 => [-2, -2, 1, -2, -2, -2, 1, 2, 1, 2, 1, 2, 1, -2, -2]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max4_check_0 : ∀ x : Fin 4,
    representation ((conjugator 3)⁻¹ * generator 0 * (conjugator 3)) ⟨x.val, by omega⟩ =
      representation (evalPair a (localWord true) (max4Words 0)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max4_check_1 : ∀ x : Fin 4,
    representation ((conjugator 3)⁻¹ * generator 1 * (conjugator 3)) ⟨x.val, by omega⟩ =
      representation (evalPair a (localWord true) (max4Words 1)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max4_check_2 : ∀ x : Fin 4,
    representation ((conjugator 3)⁻¹ * generator 2 * (conjugator 3)) ⟨x.val, by omega⟩ =
      representation (evalPair a (localWord true) (max4Words 2)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max4_check_3 : ∀ x : Fin 4,
    representation ((conjugator 3)⁻¹ * generator 3 * (conjugator 3)) ⟨x.val, by omega⟩ =
      representation (evalPair a (localWord true) (max4Words 3)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem max4_generator_eq (j : Fin 4) :
    (conjugator 3)⁻¹ * generator j * (conjugator 3) =
      evalPair a (localWord true) (max4Words j) := by
  apply eq_of_four_point_images
  fin_cases j
  · exact max4_check_0
  · exact max4_check_1
  · exact max4_check_2
  · exact max4_check_3

set_option maxRecDepth 2048 in
private theorem representative_map_le_max4 :
    representative.map (MulAut.conj (conjugator 3)⁻¹).toMonoidHom ≤
      localOvergroup true := by
  apply map_representative_le
  intro j
  change (conjugator 3)⁻¹ * generator j * ((conjugator 3)⁻¹)⁻¹ ∈ _
  rw [inv_inv, max4_generator_eq]
  exact evalPair_mem _ _ _ (a_mem_localOvergroup true)
    (localWord_mem_localOvergroup true) _

/-- Identity for max3, and the inverse of the existing max4 alignment word. -/
def fixedConjugator (i : Bool) : He :=
  if i then (conjugator 3)⁻¹ else 1

/-- Conjugates of the existing subgroup, without a new pair representative. -/
def fixedSubgroup (i : Bool) : Subgroup He :=
  representative.map (MulAut.conj (fixedConjugator i)).toMonoidHom

/-- The four conjugated generators. -/
def fixedGenerator (i : Bool) (j : Fin 4) : He :=
  MulAut.conj (fixedConjugator i) (generator j)

theorem fixedGenerator_closure (i : Bool) :
    closure (Set.range (fixedGenerator i)) = fixedSubgroup i := by
  rw [fixedSubgroup, representative, MonoidHom.map_closure, ← Set.range_comp]
  rfl

theorem fixedSubgroup_le_localOvergroup (i : Bool) :
    fixedSubgroup i ≤ localOvergroup i := by
  cases i
  · change representative.map (MonoidHom.id He) ≤ localOvergroup false
    rw [map_id]
    exact representative_le_localOvergroup
  · exact representative_map_le_max4

/-- At most 32 labelled cases: k is outside, and mask k is true. Duplicate
labels are harmless. Each entry is the closure of eight explicit words. -/
def entry (i : Bool) (k : Fin 4) (mask : Fin 4 → Bool) : Subgroup He :=
  indexTwoClosure (fixedGenerator i) k mask

theorem entry_le_fixedSubgroup (i : Bool) (k : Fin 4) (mask : Fin 4 → Bool) :
    entry i k mask ≤ fixedSubgroup i := by
  have hm (j : Fin 4) : fixedGenerator i j ∈ fixedSubgroup i :=
    fixedGenerator_closure i ▸ subset_closure (Set.mem_range_self j)
  apply (closure_le _).mpr
  rintro x ⟨e, j, rfl⟩
  unfold indexTwoGenerator
  apply mul_mem
  · exact mul_mem (by split <;> simp_all) (hm j)
  · apply inv_mem
    split <;> simp_all

/-- Exhaustiveness is proved from Schreier's lemma, independently of any
GAP subgroup list, order formula, or two-core identification. -/
theorem exists_entry_of_relIndex_two (i : Bool) (U : Subgroup He)
    (hU : U ≤ fixedSubgroup i) (hi : U.relIndex (fixedSubgroup i) = 2) :
    ∃ (k : Fin 4) (mask : Fin 4 → Bool), mask k = true ∧ entry i k mask = U :=
  exists_indexTwoClosure_of_relIndex (fixedGenerator i) (fixedSubgroup i) U
    (fixedGenerator_closure i) hU hi

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient
