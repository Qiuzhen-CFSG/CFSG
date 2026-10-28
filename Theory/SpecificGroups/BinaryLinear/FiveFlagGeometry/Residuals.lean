module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.FlagTypes
public import Theory.GroupTheory.SolvableResidual

/-!
# Embedded residuals of binary five-dimensional flag stabilizers

A proper flag stabilizer of order divisible by five has just one cut, of
dimension one or four. Both endpoint stabilizers are perfect, so their
solvable residuals map back to the whole stabilizer under the actual subgroup
inclusion. This recognizes the embedded residual without replacing it by an
abstract isomorphic group or imposing a Sylow hypothesis.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the parabolic
case A.3.12(5), printed pp.47–48, and the L₅(2) branch of 1.3.9, printed p.514.
-/

public section

open Subgroup
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic

/-- A proper flag stabilizer of order divisible by five is perfect, and its
embedded solvable residual is an actual end-node parabolic. -/
theorem endParabolic_embeddedResidual_of_five_dvd (b : FiveBasis) (cuts : Set (Fin 4))
    (hproper : flagStabilizer b cuts ≠ ⊤)
    (hfive : 5 ∣ Nat.card (flagStabilizer b cuts)) :
    FiveParabolicStabilizer.IsEndParabolic
      ((solvableResidual (flagStabilizer b cuts)).map (flagStabilizer b cuts).subtype) := by
  rcases cuts_eq_singleton_end_of_five_dvd b cuts hproper hfive with rfl | rfl
  · rw [flagStabilizer_singleton, flagSpace_zero]
    let : Group.IsPerfect (parabolic (Submodule.span (ZMod 2) {b 0})) :=
      pointParabolic_isPerfect (b.ne_zero 0)
    rw [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    exact Or.inl ⟨b 0, b.ne_zero 0, rfl⟩
  · have hf : b.coord 4 ≠ 0 := by
      intro he
      have hh := LinearMap.congr_fun he (b 4)
      simp [Module.Basis.coord_apply] at hh
    rw [flagStabilizer_singleton, flagSpace_last]
    let : Group.IsPerfect (parabolic (b.coord 4).ker) := hyperplaneParabolic_isPerfect hf
    rw [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    exact Or.inr ⟨b.coord 4, hf, rfl⟩

end BinaryLinear.FiveFlagGeometry
