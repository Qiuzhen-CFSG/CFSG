module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ResidualGeneration
public import Theory.GroupTheory.SolvableResidual.ParabolicGeneration

/-!
# Generation by the lifted symplectic-four parabolic residuals

The common flag Borel is a solvable supplement to both determinant
kernels. Applying the common-supplement theorem to their full preimages
proves generation across a solvable kernel, including noncentral kernels.
Source: Aschbacher--Smith 15.1.20(2), printed p.1095.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour
variable {X F : Type*} [Group X] [Finite X] [Group.IsPerfect X]
  [Field F] [Finite F] [CharP F 2]
/-- Both full parabolic preimages generate every perfect solvable-kernel cover. -/
theorem preimage_residuals_generate (f : X →* Sp F) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    (solvableResidual (pointParabolic.comap f)).map (pointParabolic.comap f).subtype ⊔
      (solvableResidual (planeParabolic.comap f)).map (planeParabolic.comap f).subtype = ⊤ := by
  let : Group.IsSolvable (borel (F := F)) := isSolvable_borel hF
  apply preimage_residuals_sup_eq_top f hf pointParabolic planeParabolic borel
    inf_le_left inf_le_right parabolics_sup_eq_top
  · rw [pointParabolic_solvableResidual_eq hF hn,←pointParabolic_eq_pointLocal_sup_borel]
  · rw [planeParabolic_solvableResidual_eq hF hn,←planeParabolic_eq_planeLocal_sup_borel]
end Theory.SpecificGroups.SymplecticFour
