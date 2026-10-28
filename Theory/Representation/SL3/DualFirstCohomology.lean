module
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeLargeField
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.SL3.DualLiftCentralizers
public import Theory.Combinatorics.ProjectivePlaneMatrixAction

/-!
# First cohomology of the nonbinary dual SL₃ module

Inverse transpose and the actual covector coordinates transport the
natural-module vanishing theorem to its dual over every finite field
with more than two elements. This is the dual case needed for the
C.1.35 action normalizer, Aschbacher–Smith, printed p.138.
-/


public section
open scoped MatrixGroups
namespace Representation.OneCohomology.SLHigherNatural
open Representation.SL3ParabolicNatural
variable {F : Type*} [Field F] [Finite F]

theorem H1_subsingleton_sl3_dual_large_field (hF : 2 < Nat.card F) :
    Subsingleton (H1 (specialLinearNatural (k := F) 3).dual) := by
  let := H1_subsingleton_sl3_large_field hF
  let g : SL(3,F) →* SL(3,F) := Matrix.SpecialLinearGroup.inverseTranspose
  have hg (a : SL(3,F)) : g (g a) = a := by
    change ((g a)⁻¹).transpose = a
    rw [← map_inv]
    change ((a⁻¹)⁻¹).transpose.transpose = a
    rw [inv_inv]
    apply Subtype.ext
    rfl
  let eG : SL(3,F) ≃* SL(3,F) := { g with
    invFun := g
    left_inv := hg
    right_inv := hg }
  let e := H1Congr (specialLinearNatural (k := F) 3).dual
    (specialLinearNatural (k := F) 3) eG dualVectorCoordinates
    (fun a v => dualVectorCoordinates_action a v)
  exact e.injective.subsingleton
end Representation.OneCohomology.SLHigherNatural
