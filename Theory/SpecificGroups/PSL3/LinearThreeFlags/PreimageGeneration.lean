module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.GroupTheory.SolvableResidual.ParabolicGeneration

/-!
# Generation by the lifted linear-three parabolic residuals

The standard flag Borel is solvable and supplements both perfect local
factors. The common-supplement theorem therefore lifts their generation
through any solvable kernel; no centrality or splitting is needed.
Source: Aschbacher--Smith 15.1.20(2), printed p.1095.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable {X F : Type*} [Group X] [Finite X] [Group.IsPerfect X]
  [Field F] [Finite F]
/-- Both full parabolic preimages generate every perfect solvable-kernel cover. -/
theorem preimage_residuals_generate (f : X →* SL(3,F)) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    (solvableResidual ((pointParabolicSL F).comap f)).map ((pointParabolicSL F).comap f).subtype ⊔
      (solvableResidual ((lineParabolicSL F).comap f)).map ((lineParabolicSL F).comap f).subtype = ⊤ := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  let : Group.IsSolvable (projection F).ker := by
    rw [projection_ker]
    exact Group.isSolvable_of_comm (fun x y => mul_comm' x y)
  let : Group.IsSolvable (borel F) := BorelStructure.borel_isSolvable F hF
  let : Group.IsSolvable (borelSL F) := by
    rw [←borel_comap F]
    exact isSolvable_comap_of_solvable_ker _ _
  apply preimage_residuals_sup_eq_top f hf (pointParabolicSL F) (lineParabolicSL F)
    (borelSL F) inf_le_left inf_le_right (parabolicsSL_sup_eq_top F)
  · rw [pointParabolicSL_residual F hfour,←pointParabolicSL_eq_sup F]
  · rw [lineParabolicSL_residual F hfour,←lineParabolicSL_eq_sup F]
end Matrix.PSL3.LinearThree
