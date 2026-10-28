module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.NormalizedPresentation
import Mathlib.Tactic.Group

/-!
# Central errors in the normalized Parrott presentation

Each original relator commutes with the ten generators by the defining
auxiliary relations. Free-group induction extends this to every word.
These central errors are the coefficients used in the power/root calculation.

Source: Parrott (1972), §5, p.683; the auxiliary presentation and its
normalization equations are defined in the imported module.
-/

public section

open Tits
namespace Tits.CentralCoverLifting.CompatibleGenerators
/-- The defining generator commutations make each original relator central. -/
theorem powerRoot_normalizedGenerator_relators_central (j : ParrottRelatorIndex) :
    FreeGroup.lift normalizedGenerator (parrottRelator j) ∈ Subgroup.center NormalizedPresentation := by
  have hh : FreeGroup.lift normalizedGenerator = PresentedGroup.mk normalizedRelatorSet := by
    ext i
    rfl
  let z := FreeGroup.lift normalizedGenerator (parrottRelator j)
  have hg (i : ParrottGenerator) : Commute z (normalizedGenerator i) := by
    have h : FreeGroup.lift normalizedGenerator
        (parrottCommutator (parrottRelator j) (FreeGroup.of i)) = 1 := by
      rw [hh]
      exact PresentedGroup.one_of_mem ⟨.inl (j, i), rfl⟩
    simp only [parrottCommutator, map_mul, map_inv, FreeGroup.lift_apply_of] at h
    change z⁻¹ * (normalizedGenerator i)⁻¹ * z * normalizedGenerator i = 1 at h
    change z * normalizedGenerator i = normalizedGenerator i * z
    calc
      _ = normalizedGenerator i * z *
          (z⁻¹ * (normalizedGenerator i)⁻¹ * z * normalizedGenerator i) := by group
      _ = _ := by rw [h, mul_one]
  rw [Subgroup.mem_center_iff]
  intro x
  change Commute x z
  apply PresentedGroup.induction_on x
  intro w
  rw [← hh]
  change Commute (FreeGroup.lift normalizedGenerator w) z
  induction w using FreeGroup.induction_on with
  | C1 => exact Commute.one_left z
  | of i => exact (hg i).symm
  | inv_of i => simpa using (hg i).symm.inv_left
  | mul x y hx hy => simpa using hx.mul_left hy
/-- The actual central error of a source relator, before its vanishing is proved. -/
@[expose] def normalizedRelatorError (j : ParrottRelatorIndex) :
    Subgroup.center NormalizedPresentation :=
  ⟨FreeGroup.lift normalizedGenerator (parrottRelator j),
    powerRoot_normalizedGenerator_relators_central j⟩

/-- Vanishing of the central error is precisely the original word equation. -/
theorem normalizedRelatorError_eq_one_iff (j : ParrottRelatorIndex) :
    normalizedRelatorError j = 1 ↔
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 := by
  exact Subtype.ext_iff

end Tits.CentralCoverLifting.CompatibleGenerators
