module

public import Theory.Representation.PSL3Two.SmallModules
public import Theory.Representation.FirstCohomologyProjective
public import Theory.Representation.ProjectiveTrace
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
import Mathlib.Tactic.FinCases

/-!
# Projectivity of the binary Steinberg module

Take the coordinate projection onto the matrix unit E₀₁ in the literal
trace-zero adjoint module. A kernel-checked finite sum says that its group
trace fixes E₀₁. Irreducibility makes that trace the identity. The general
trace criterion then gives projectivity over F₂[SL₃(2)], and hence vanishing
of the actual first cohomology.

Source: Aschbacher–Smith, H.6.3(1), printed p.387, and Remark I.1.5,
printed p.408, combined manuscript of 1 March 2004. The eight-dimensional
projective factor is used in B.4.11, printed p.96.
-/

public section

open Matrix Representation
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue
open scoped MonoidAlgebra
noncomputable section

namespace BinaryLinearThree.SteinbergStructure

private def seed : Steinberg := coordinates.symm (Pi.single 0 1)

private def seedAction (g : Group) : Eight :=
  ![g.val 0 0 * g⁻¹.val 1 1, g.val 0 0 * g⁻¹.val 1 2,
    g.val 1 0 * g⁻¹.val 1 0, g.val 1 0 * g⁻¹.val 1 2,
    g.val 2 0 * g⁻¹.val 1 0, g.val 2 0 * g⁻¹.val 1 1,
    g.val 0 0 * g⁻¹.val 1 0, g.val 1 0 * g⁻¹.val 1 1]

private theorem coordinates_seed (g : Group) : coordinates (S g seed) = seedAction g := by
  change readMatrix (LinearMap.toMatrix'
    (W g ∘ₗ (matrixOf (Pi.single 0 1)).toLin' ∘ₗ W g⁻¹)) = _
  have hm (h : Group) : LinearMap.toMatrix' (W h) = h.val :=
    LinearMap.toMatrix'_toLin' h.val
  simp only [LinearMap.toMatrix'_comp, hm, LinearMap.toMatrix'_toLin']
  ext i
  fin_cases i <;> simp [seedAction, readMatrix, matrixOf, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, Fin.sum_univ_three]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem norm_seed_certificate :
    ∑ g : Group, (seedAction g 0) • seedAction g⁻¹ = Pi.single 0 1 := by
  simp only [seedAction, inv_inv]
  ext i
  fin_cases i <;> decide +kernel

private def projection : Module.End (ZMod 2) Steinberg :=
  ((LinearMap.proj (0 : Fin 8)).comp coordinates.toLinearMap).smulRight seed

private theorem seed_ne_zero : seed ≠ 0 := by
  intro h
  have hh := congrArg (fun v : Steinberg => coordinates v 0) h
  simp [seed] at hh

private theorem norm_projection_seed : ∑ g : Group, S g⁻¹ (projection (S g seed)) = seed := by
  apply coordinates.injective
  rw [map_sum]
  simp only [projection, LinearMap.smulRight_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearEquiv.coe_coe, map_smul, coordinates_seed]
  simpa only [seed, LinearEquiv.apply_symm_apply] using norm_seed_certificate

/-- H.6.3(1): the literal trace-zero adjoint module is projective over the group algebra. -/
theorem projective : Module.Projective (ZMod 2)[Group] S.asModule := by
  let : IsIrreducible S := steinberg_irreducible
  exact Representation.ProjectiveTrace.projective_of_norm_fixed S projection seed
    seed_ne_zero norm_projection_seed

/-- The projective Steinberg module has vanishing first cohomology. -/
theorem subsingleton_H1 : Subsingleton (Representation.OneCohomology.H1 S) := by
  let : Module.Projective (ZMod 2)[Group] S.asModule := projective
  exact Representation.OneCohomology.subsingleton_H1_of_projective S

end BinaryLinearThree.SteinbergStructure
end
