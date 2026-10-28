module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.NaturalAction
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.TensorGeometry
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SpinIrreducible

/-!
# The concrete natural–spin tensor action

The actual 24-dimensional coordinate-halfspace module and the actual
4096-dimensional signed Parker-axis spin module give a fixed real tensor
space of dimension 98304. Their tensor action is monomial, preserves the
positive definite tensor form, and has kernel exactly the specified `K`.
Consequently the actual local quotient `N1/K` acts faithfully on this space.
All hypotheses of the independent tensor-kernel and geometry arguments are
proved for these fixed factors.

This is the tensor action used in Aschbacher, *Sporadic Groups*, Lemma 27.5,
printed p. 147. The spin carrier here is the signed space on `A2 ∪ A3`.
`DirectSumAction` and `SourceComparisons` construct the equivariant isometries
to the displayed spin direct sum and its natural tensor product, respectively.
-/

@[expose] public section
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped TensorProduct
namespace Sporadic.Monster.Construction.TrialitySpin.TensorAction
open SignedModules.Natural

-- Reuse the canonical additive structures through the nested tensor subtype.
local instance : AddCommGroup B1_24 := inferInstance
local instance : AddCommGroup SpinSpace := inferInstance

abbrev Space := B1_24 ⊗[ℝ] SpinSpace

/-- The fixed tensor representation of the concrete source subgroup. -/
def representation : Representation ℝ N1 Space :=
  TensorKernel.representation NaturalAction.representation

theorem finrank_space : Module.finrank ℝ Space = 98304 :=
  TensorKernel.finrank_tensor (SignedModules.Natural.finrank_space 0)

instance space_nontrivial : Nontrivial Space :=
  Module.nontrivial_of_finrank_pos (by rw [finrank_space]; norm_num)

private theorem natural_nontrivial : Nontrivial B1_24 :=
  Module.nontrivial_of_finrank_pos (by rw [SignedModules.Natural.finrank_space 0]; norm_num)

/-- The specified four-group is exactly the kernel; no action premises remain. -/
theorem representation_kernel : representation.ker = K.subgroupOf N1 := by
  let : Nontrivial B1_24 := natural_nontrivial
  exact TensorKernel.kernel_eq_K NaturalAction.representation
    NaturalAction.representation_of_mem_Q1 NaturalAction.representation_c

theorem representation_z : representation SpinAction.z = -(1 : Module.End ℝ Space) :=
  TensorKernel.representation_z NaturalAction.representation NaturalAction.representation_of_mem_Q1

theorem representation_c : representation SpinAction.c = -(1 : Module.End ℝ Space) := by
  apply TensorProduct.ext'
  intro v s
  simp only [representation, TensorKernel.representation, Representation.tprod_apply,
    TensorProduct.map_tmul, NaturalAction.representation_c, SpinAction.representation_c,
    LinearMap.neg_apply, Module.End.one_apply, TensorProduct.neg_tmul]

/-- The fixed positive definite tensor form. -/
def form : LinearMap.BilinForm ℝ Space := TensorGeometry.form (SignedModules.Natural.form 0)

/-- The natural positive labels tensored with a transversal of spin signs. -/
def basis : Module.Basis (Atlas.Codes.Omega × bothAxesDomain.signedOrbits.toPairing.Orbit)
    ℝ Space := TensorGeometry.basis (SignedModules.Natural.basis 0)

theorem form_tmul (v w : B1_24) (s t : SpinSpace) :
    form (v ⊗ₜ[ℝ] s) (w ⊗ₜ[ℝ] t) = SignedModules.Natural.form 0 v w *
      bothAxesDomain.form s t := TensorGeometry.form_tmul _ v w s t

theorem form_pos (v : Space) (hv : v ≠ 0) : 0 < form v v :=
  TensorGeometry.form_pos _ (SignedModules.Natural.basis 0)
    (fun i j => by
      by_cases h : i = j <;> simp only [SignedModules.Natural.basis_orthonormal, h, ↓reduceIte]) v hv

theorem basis_orthonormal (i j : Atlas.Codes.Omega ×
    bothAxesDomain.signedOrbits.toPairing.Orbit) :
    form (basis i) (basis j) = if i = j then 1 else 0 := by
  classical
  have h := TensorGeometry.basis_orthonormal (SignedModules.Natural.form 0) (SignedModules.Natural.basis 0)
    (fun i j => by
      by_cases h : i = j <;> simp only [SignedModules.Natural.basis_orthonormal, h, ↓reduceIte]) i j
  by_cases hij : i = j <;> simpa only [form, basis, hij, ↓reduceIte] using h

theorem representation_isometry (g : N1) (v w : Space) :
    form (representation g v) (representation g w) = form v w :=
  TensorGeometry.representation_isometry _ NaturalAction.representation
    NaturalAction.representation_isometry g v w

theorem representation_monomial (g : N1) (i : Atlas.Codes.Omega ×
    bothAxesDomain.signedOrbits.toPairing.Orbit) :
    ∃ j, representation g (basis i) = basis j ∨ representation g (basis i) = -basis j :=
  TensorGeometry.representation_monomial (SignedModules.Natural.basis 0)
    NaturalAction.representation NaturalAction.representation_monomial g i

/-- The concrete faithful representation of the literal local quotient. -/
def quotientRepresentation : Representation ℝ N1Quotient Space :=
  TensorKernel.quotientRepresentation NaturalAction.representation
    NaturalAction.representation_of_mem_Q1 NaturalAction.representation_c

theorem quotientRepresentation_mk (g : N1) :
    quotientRepresentation (QuotientGroup.mk' (K.subgroupOf N1) g) = representation g := rfl

theorem quotientRepresentation_faithful : Function.Injective quotientRepresentation := by
  let : Nontrivial B1_24 := natural_nontrivial
  exact TensorKernel.quotientRepresentation_faithful NaturalAction.representation
    NaturalAction.representation_of_mem_Q1 NaturalAction.representation_c

/-- The same action on the actual image of `N1` in `N/K`, for local-group consumers. -/
def imageRepresentation : Representation ℝ N1Image Space :=
  quotientRepresentation.comp n1QuotientEquivImage.symm.toMonoidHom

theorem imageRepresentation_faithful : Function.Injective imageRepresentation :=
  quotientRepresentation_faithful.comp n1QuotientEquivImage.symm.injective

theorem imageRepresentation_map (g : N1) :
    imageRepresentation (n1ImageMap g) = representation g := by
  change quotientRepresentation (n1QuotientEquivImage.symm (n1ImageMap g)) = _
  rw [← n1QuotientEquivImage_mk, n1QuotientEquivImage.symm_apply_apply]
  rfl

end Sporadic.Monster.Construction.TrialitySpin.TensorAction
