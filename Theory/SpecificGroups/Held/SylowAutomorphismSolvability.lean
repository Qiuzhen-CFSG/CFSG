module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile
public import Mathlib.GroupTheory.Nilpotent

/-!
# The Held Sylow representative has a two-group automorphism group

Its actual Frattini quotient has sixteen vectors. The intrinsic order-four
fiber profile forces every induced automorphism to have fourth power one.
The Burnside basis-kernel theorem makes the kernel a two-group as well, so
Aut(P) is a two-group and in particular is solvable. The map, kernel equality,
profile, and quotient bound are all proved for the original representative;
no simplicity or automorphism-realization assumption is used.

Source: the ATLAS HeG1-p2058B0 Sylow words and their checked collection and
Frattini coordinates. The intended application is the Held full outer-
solvability input in Aschbacher--Smith A.3.9.
-/

namespace Held.SylowAutomorphismSolvability
open FrattiniCoordinates OrderFourProfile

public theorem representative_mulAut_isPGroup :
    IsPGroup 2 (MulAut Held.LocalPairs.SylowGeometry.Calculations.representative) := by
  obtain ⟨f, hf, hker, hgen⟩ := exists_frattini_coordinate
  apply MonoidHom.isPGroup_mulAut_of_frattini_predicateFiber
    Held.LocalPairs.SylowGeometry.Calculations.representative_isPGroup f hf hker
    (fun _ : Unit => fun x => x ^ 4 = 1 ∧ x ^ 2 ≠ 1)
  · intro b _ x
    simp only [← map_pow, ne_eq, b.map_eq_one_iff]
  · intro b hb
    refine ⟨2, ?_⟩
    apply profile_preserving_pow_four
    intro v
    rw [← orderFour_fiber_card f hgen (b v), ← orderFour_fiber_card f hgen v]
    exact hb () v

public theorem representative_mulAut_isSolvable :
    Group.IsSolvable (MulAut Held.LocalPairs.SylowGeometry.Calculations.representative) := by
  let := representative_mulAut_isPGroup.isNilpotent
  infer_instance
end Held.SylowAutomorphismSolvability
