module

public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative
public import Theory.SpecificGroups.Held.Model.FourPointBase
import Mathlib.Tactic.FinCases

/-!
# The fixed Held subgroup lies in each two-local candidate

Explicit conjugates of the four-word subgroup in `Calculations.Representative`
lie in the literal ATLAS max3, max4 and max5 subgroups. For max3 this is already
proved by its definition. For max4 and max5, four generator identities are
checked on the certified four-point base and then extended by subgroup closure.
The word witnesses and their GAP reproduction are retained in
`SylowContainment/source`. The original candidate definitions are unchanged.

No claim of Sylow status is needed for this containment calculation. Once the
representative is known to be Sylow and self-normalizing, these containments
allow the Frattini argument to prove self-normalization of all three candidates.

Source: the literal ATLAS HeG1-p2058B0 and max3/max4/max5 programs;
GLS3 Table 5.3p. GAP discovers the words; Lean checks the identities.
-/

namespace Held.TwoLocalCandidates.SylowContainment
open Subgroup LocalPairs.PairCoverage
open LocalPairs.SylowGeometry.Calculations

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

private def max4Conjugator : He := evalPair a b [-1, -2, -1, -2, -1, -2, -1, -2, -2, -2, -1, 2, 2, -1, 2, -1, 2, 2]

private def max4Words : Fin 4 → List ℤ
  | 0 => [1, -2, 1, 2, 1, 2, 2, 1, -2, -2, 1, -2, 1, 2, 1]
  | 1 => [-2, -2, -2, 1, 2, 1, 2, 2, 1, 2, 1, -2, -2, 1, 2, 2, 1, 2]
  | 2 => [-2, 1, -2, 1, 2, 1, 2]
  | 3 => [-2, -2, 1, -2, -2, -2, 1, 2, 1, 2, 1, 2, 1, -2, -2]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max4_check_0 : ∀ x : Fin 4,
    representation (max4Conjugator⁻¹ * generator 0 * max4Conjugator) ⟨x.val, by omega⟩ =
      representation (evalPair (a) (localWord true) (max4Words 0)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max4_check_1 : ∀ x : Fin 4,
    representation (max4Conjugator⁻¹ * generator 1 * max4Conjugator) ⟨x.val, by omega⟩ =
      representation (evalPair (a) (localWord true) (max4Words 1)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max4_check_2 : ∀ x : Fin 4,
    representation (max4Conjugator⁻¹ * generator 2 * max4Conjugator) ⟨x.val, by omega⟩ =
      representation (evalPair (a) (localWord true) (max4Words 2)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max4_check_3 : ∀ x : Fin 4,
    representation (max4Conjugator⁻¹ * generator 3 * max4Conjugator) ⟨x.val, by omega⟩ =
      representation (evalPair (a) (localWord true) (max4Words 3)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem max4_generator_eq (j : Fin 4) :
    max4Conjugator⁻¹ * generator j * max4Conjugator =
      evalPair (a) (localWord true) (max4Words j) := by
  apply eq_of_four_point_images
  fin_cases j
  · exact max4_check_0
  · exact max4_check_1
  · exact max4_check_2
  · exact max4_check_3

set_option maxRecDepth 2048 in
private theorem representative_map_le_max4 :
    representative.map (MulAut.conj max4Conjugator⁻¹).toMonoidHom ≤
      localOvergroup true := by
  apply map_representative_le
  intro j
  change max4Conjugator⁻¹ * generator j * (max4Conjugator⁻¹)⁻¹ ∈ _
  rw [inv_inv, max4_generator_eq]
  exact evalPair_mem _ _ _ (a_mem_localOvergroup true)
    (localWord_mem_localOvergroup true) _

private def max5Conjugator : He := evalPair a b [1, 2, 1, 2, 1, 2, 2, 1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -2]

private def max5Words : Fin 4 → List ℤ
  | 0 => [-2, 1, 1, 2, 1, -2, 1, 2, 1, 2, -1, -2, 1, -2, 1]
  | 1 => [2, -1, 2, 1, 2, -1, -1, -2, -1, 2, 1, -2, -1]
  | 2 => [1, -2, 1, 2, 1, 2, -1, -1, 2, 1, 2]
  | 3 => [2, 1, 2, 1, 2, -1, 2, 1, 1, 2]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max5_check_0 : ∀ x : Fin 4,
    representation (max5Conjugator⁻¹ * generator 0 * max5Conjugator) ⟨x.val, by omega⟩ =
      representation (evalPair (max5First) (max5Second) (max5Words 0)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max5_check_1 : ∀ x : Fin 4,
    representation (max5Conjugator⁻¹ * generator 1 * max5Conjugator) ⟨x.val, by omega⟩ =
      representation (evalPair (max5First) (max5Second) (max5Words 1)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max5_check_2 : ∀ x : Fin 4,
    representation (max5Conjugator⁻¹ * generator 2 * max5Conjugator) ⟨x.val, by omega⟩ =
      representation (evalPair (max5First) (max5Second) (max5Words 2)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem max5_check_3 : ∀ x : Fin 4,
    representation (max5Conjugator⁻¹ * generator 3 * max5Conjugator) ⟨x.val, by omega⟩ =
      representation (evalPair (max5First) (max5Second) (max5Words 3)) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem max5_generator_eq (j : Fin 4) :
    max5Conjugator⁻¹ * generator j * max5Conjugator =
      evalPair (max5First) (max5Second) (max5Words j) := by
  apply eq_of_four_point_images
  fin_cases j
  · exact max5_check_0
  · exact max5_check_1
  · exact max5_check_2
  · exact max5_check_3

set_option maxRecDepth 2048 in
private theorem representative_map_le_max5 :
    representative.map (MulAut.conj max5Conjugator⁻¹).toMonoidHom ≤
      max5 := by
  apply map_representative_le
  intro j
  change max5Conjugator⁻¹ * generator j * (max5Conjugator⁻¹)⁻¹ ∈ _
  rw [inv_inv, max5_generator_eq]
  exact evalPair_mem _ _ _ max5First_mem max5Second_mem _

/-- Each literal two-local candidate contains an explicit conjugate of the
same published four-word subgroup. This theorem does not assume it is Sylow. -/
public theorem exists_conjugate_representative_le (i : Fin 3) :
    ∃ g : He, representative.map (MulAut.conj g).toMonoidHom ≤ subgroup i := by
  fin_cases i
  · refine ⟨1, ?_⟩
    have he : (MulAut.conj (1 : He)).toMonoidHom = MonoidHom.id He := by
      ext x
      simp
    change representative.map (MulAut.conj (1 : He)).toMonoidHom ≤ localOvergroup false
    rw [he, Subgroup.map_id]
    exact representative_le_localOvergroup
  · exact ⟨max4Conjugator⁻¹, representative_map_le_max4⟩
  · exact ⟨max5Conjugator⁻¹, representative_map_le_max5⟩

end Held.TwoLocalCandidates.SylowContainment
