module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Marking
public import Mathlib.GroupTheory.PGroup
import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
import Theory.SpecificGroups.Held.Model.FourPointBase
import Mathlib.Tactic.FinCases

/-!
# The common Held marking is a two-group

Four explicit word identities conjugate the marked generators into the
concrete subgroup `SylowGeometry.Calculations.representative`. Its two-group
property was proved from checked power and conjugation identities, without
assuming local subgroup structure. The audited four-point base checks the
bridge in the actual Held carrier. Closure and injective transport finish
the proof; no order, Sylow or exhaustive-placement assertion is needed.

Sources: ATLAS HeG1-p2058B0 and HeG1-max3W1; GLS3, Table 5.3p.
The new bridge words and a GAP diagnostic are retained in `source/`.
The carrier already inverts GAP permutations, so word order is preserved.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups
open Held.LocalPairs.SylowGeometry.Calculations

private def transporter : He :=
  wordEval a (localWord false)
    [(true, 1), (false, 1), (true, -2), (false, 1), (true, -4), (false, 1),
      (true, -1), (false, -1), (true, -1), (false, -1), (true, 1)]

private def imageWord : Fin 4 → List (Fin 4 × ℤ)
  | 0 => [(0, -1), (1, -1), (0, -1)]
  | 1 => [(2, -1)]
  | 2 => [(3, -3), (1, 1), (0, 1), (1, 1), (3, -1)]
  | 3 => [(3, -2), (0, -1), (1, -1), (3, -1), (1, -1), (0, -1)]

private def imageElement (i : Fin 4) : He :=
  ((imageWord i).map (fun p => generator p.1 ^ p.2)).prod

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem bridge (i : Fin 4) :
    transporter⁻¹ * markedGenerator i * transporter = imageElement i := by
  fin_cases i <;> apply eq_of_four_point_images <;> decide +kernel

private theorem image_mem (i : Fin 4) : imageElement i ∈ representative := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  exact representative.zpow_mem (generator_mem p.1) p.2

/-- The actual four-word marking is a two-group, by an explicit conjugation
into a concretely certified two-group. -/
public theorem markedSubgroup_isPGroup : IsPGroup 2 markedSubgroup := by
  have hle : markedSubgroup ≤ representative.comap
      (MulAut.conj transporter⁻¹).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change transporter⁻¹ * markedGenerator i * (transporter⁻¹)⁻¹ ∈ representative
    rw [inv_inv, bridge]
    exact image_mem i
  exact (representative_isPGroup.comap_of_injective
    (MulAut.conj transporter⁻¹).toMonoidHom (MulAut.conj transporter⁻¹).injective).of_injective
      (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end Held.LocalPairs.PairCoverage.SylowOvergroups
