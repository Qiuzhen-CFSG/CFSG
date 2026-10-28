module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.HigherUnitary
public import Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.CoreCentralizer

/-!
# Applying the unitary flag-kernel calculation to B.1.13

The concrete normal two-subgroup and projective lifting results discharge the
intrinsic parabolic two-core premise of the existing higher-unitary consumer,
conditional on the remaining matrix centralizer calculation. The placement
input remains independent. Neither remaining geometric input is asserted here.

Source: Aschbacher--Smith B.1.13, printed p.74 (PDF p.85), and GLS3 2.6.5(e).
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryRootNormalizer
open Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics
open Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.CoreCentralizer

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.HigherUnitary

/-- The radical calculation feeds the literal higher-unitary Sylow-overgroup
consumer. Exhaustive placement and the scalar-shear matrix calculation are
independent remaining source inputs, to be discharged by their assembly owners. -/
theorem properSylowFittingBound_of_scalarShear_calculation
    {F : Type*} [Field F] [Finite F] {d : ℕ} (J : HermitianForm d F)
    (hd : 4 ≤ d) (a : ℕ) (ha : 0 < a) (hcard : Nat.card F = (2 ^ a) ^ 2)
    (hplacement : ∀ (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
      (X : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      (S : Subgroup _) ≤ X → X ≠ ⊤ →
      ∃ W : Submodule F (Fin d → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
        TotallyIsotropic J W ∧ X ≤ parabolic J W)
    (hcalc : ∀ (W : Submodule F (Fin d → F)), W ≠ ⊥ → W ≠ ⊤ →
      TotallyIsotropic J W → ∀ g : specialStabilizer J W,
      g ∈ centralizer (specialRadical J W : Set (specialStabilizer J W)) →
        ScalarShear J W g) :
    ProperSylowFittingBound (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : CharP F 2 := charP_binary ha hcard
  let : NeZero d := ⟨by omega⟩
  apply properSylowFittingBound_of_isotropic_placement J hplacement
  intro W hW hWtop hi
  exact centralizer_twoCore_le_of_scalarShear J W hW hi (hcalc W hW hWtop hi)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.HigherUnitary
