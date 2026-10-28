module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.HalfComparisons
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.DirectSumAction
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.TensorAction

/-!
# Source natural and tensor comparisons

The loop and standard generators act on the first natural space by the
coordinate formulas of 27.4. Tensoring the explicit spin restriction with
the identity on the natural factor gives an equivariant isometry to the
source's displayed natural-by-direct-sum tensor space. Consequently the
kernel in Lemma 27.5 is `K` for that displayed realization as well.

Source: Aschbacher, *Sporadic Groups*, Lemmas 27.4–27.5, printed pp. 146–147.
The full action of `N` on the Griess space is a subsequent construction.
-/

@[expose] public section
noncomputable section
attribute [local instance] Classical.propDecidable
open Atlas.Fischer Atlas.Codes
open scoped TensorProduct
namespace Sporadic.Monster.Construction.TrialitySpin

namespace NaturalAction
open SignedModules.Natural

theorem representation_psiOne_L (d : ParkerLoop) (x : Omega) (ε : ParkerBit) :
    representation (HalfActions.inclusion (HalfActions.psiOne d)) (L 0 ε x) = L 0 ε x := by
  change SignedModules.Natural.representation SpinAction.permutations preserves_halfspaces _ _ = _
  have h : SpinAction.permutations (HalfActions.inclusion (HalfActions.psiOne d)) ''
      halfspace 0 (x,ε) = halfspace 0 (x,ε) := psi_self_halfspace 0 d (x,ε)
  rw [SignedModules.Natural.representation_L, labelEquiv_of_image _ _ _ _ h]

theorem representation_psiTwo_L (d : ParkerLoop) (x : Omega) (ε : ParkerBit) :
    representation (HalfActions.inclusion (HalfActions.psiTwo d)) (L 0 ε x) =
      L 0 (ε + d.1.val x) x := by
  change SignedModules.Natural.representation SpinAction.permutations preserves_halfspaces _ _ = _
  have h : SpinAction.permutations (HalfActions.inclusion (HalfActions.psiTwo d)) ''
      halfspace 0 (x,ε) = halfspace 0 (x,ε + d.1.val x) := psi_other_halfspace 1 0 (by decide) d x ε
  rw [SignedModules.Natural.representation_L, labelEquiv_of_image _ _ _ _ h]

theorem representation_psiThree_L (d : ParkerLoop) (x : Omega) (ε : ParkerBit) :
    representation (HalfActions.inclusion (HalfActions.psiThree d)) (L 0 ε x) =
      L 0 (ε + d.1.val x) x := by
  change SignedModules.Natural.representation SpinAction.permutations preserves_halfspaces _ _ = _
  have h : SpinAction.permutations (HalfActions.inclusion (HalfActions.psiThree d)) ''
      halfspace 0 (x,ε) = halfspace 0 (x,ε + d.1.val x) := psi_other_halfspace 2 0 (by decide) d x ε
  rw [SignedModules.Natural.representation_L, labelEquiv_of_image _ _ _ _ h]

theorem representation_standard_L (α : ParkerStandardGroup) (x : Omega) (ε : ParkerBit) :
    representation (DirectSumAction.standard α) (L 0 ε x) =
      L 0 ε ((parkerStandardProjection α).val x) := by
  change SignedModules.Natural.representation SpinAction.permutations preserves_halfspaces _ _ = _
  have h : SpinAction.permutations (DirectSumAction.standard α) '' halfspace 0 (x,ε) =
      halfspace 0 ((parkerStandardProjection α).val x,ε) := standard_self_halfspace 0 α x ε
  rw [SignedModules.Natural.representation_L, labelEquiv_of_image _ _ _ _ h]

/-- The other two generators of `K` invert the natural factor, as in 27.4(4). -/
theorem representation_kTwo : representation SpinAction.kTwo = -1 :=
  TensorKernel.natural_kTwo representation representation_of_mem_Q1 representation_c

theorem representation_kThree : representation SpinAction.kThree = -1 := by
  rw [SpinAction.kThree_eq_kOne_mul_kTwo, map_mul,
    TensorKernel.natural_kOne representation representation_of_mem_Q1,
    one_mul, representation_kTwo]

end NaturalAction

namespace TensorAction
open SignedModules.Natural SpinActions

local instance : AddCommGroup B1_24 := inferInstance
local instance : AddCommGroup SpinSpace := inferInstance
local instance : AddCommGroup SpinDirectSum := inferInstance

/-- The literal natural-by-two-halves tensor space in the source. -/
abbrev DirectSumSpace := B1_24 ⊗[ℝ] SpinDirectSum

def restriction : Space ≃ₗ[ℝ] DirectSumSpace :=
  TensorProduct.congr (LinearEquiv.refl ℝ B1_24) spinRestriction

theorem restriction_tmul (v : B1_24) (s : SpinSpace) :
    restriction (v ⊗ₜ[ℝ] s) = v ⊗ₜ[ℝ] spinRestriction s := rfl

/-- The tensor of the two constructed source representations. -/
def directSumRepresentation : Representation ℝ N1 DirectSumSpace :=
  NaturalAction.representation.tprod DirectSumAction.representation

theorem restriction_equivariant (g : N1) (v : Space) :
    restriction (representation g v) = directSumRepresentation g (restriction v) := by
  have h : restriction.toLinearMap.comp (representation g) =
      (directSumRepresentation g).comp restriction.toLinearMap := by
    apply TensorProduct.ext'
    intro v s
    change restriction (NaturalAction.representation g v ⊗ₜ[ℝ] SpinAction.representation g s) =
      NaturalAction.representation g v ⊗ₜ[ℝ] DirectSumAction.representation g (spinRestriction s)
    rw [restriction_tmul, DirectSumAction.representation_restriction]
  exact LinearMap.congr_fun h v

def restrictionEquiv : representation.Equiv directSumRepresentation :=
  .mk restriction (fun g => LinearMap.ext (restriction_equivariant g))

/-- Source 27.5(3), in the displayed natural-by-direct-sum realization. -/
theorem directSumRepresentation_kernel : directSumRepresentation.ker = K.subgroupOf N1 := by
  rw [← representation_kernel]
  ext g
  change directSumRepresentation g = 1 ↔ representation g = 1
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    apply restriction.injective
    rw [restriction_equivariant, h]
    rfl
  · intro h
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := restriction.surjective v
    rw [← restriction_equivariant, h]
    rfl

def directSumForm : LinearMap.BilinForm ℝ DirectSumSpace :=
  form.compl₁₂ restriction.symm.toLinearMap restriction.symm.toLinearMap

theorem restriction_isometry (v w : Space) :
    directSumForm (restriction v) (restriction w) = form v w := by
  change form (restriction.symm (restriction v)) (restriction.symm (restriction w)) = _
  rw [restriction.symm_apply_apply, restriction.symm_apply_apply]

/-- The transported form is precisely the tensor product of the source factor forms. -/
theorem directSumForm_tmul (v w : B1_24) (s t : SpinDirectSum) :
    directSumForm (v ⊗ₜ[ℝ] s) (w ⊗ₜ[ℝ] t) =
      SignedModules.Natural.form 0 v w * SpinDirectSum.form s t := by
  obtain ⟨s,rfl⟩ := spinRestriction.surjective s
  obtain ⟨t,rfl⟩ := spinRestriction.surjective t
  rw [← restriction_tmul, ← restriction_tmul, restriction_isometry,
    form_tmul, DirectSumAction.restriction_isometry]

theorem directSumForm_pos (v : DirectSumSpace) (hv : v ≠ 0) :
    0 < directSumForm v v :=
  form_pos (restriction.symm v) (fun h => hv (restriction.symm.injective (by simpa using h)))

theorem directSumRepresentation_isometry (g : N1) (v w : DirectSumSpace) :
    directSumForm (directSumRepresentation g v) (directSumRepresentation g w) =
      directSumForm v w := by
  obtain ⟨v,rfl⟩ := restriction.surjective v
  obtain ⟨w,rfl⟩ := restriction.surjective w
  rw [← restriction_equivariant, ← restriction_equivariant,
    restriction_isometry, restriction_isometry, representation_isometry]

/-- An orthonormal basis in the displayed tensor realization. -/
def directSumBasis : Module.Basis (Omega × bothAxesDomain.signedOrbits.toPairing.Orbit)
    ℝ DirectSumSpace := basis.map restriction

theorem directSumBasis_orthonormal (i j : Omega × bothAxesDomain.signedOrbits.toPairing.Orbit) :
    directSumForm (directSumBasis i) (directSumBasis j) = if i = j then 1 else 0 := by
  change directSumForm (restriction (basis i)) (restriction (basis j)) = _
  rw [restriction_isometry, basis_orthonormal]

theorem directSumRepresentation_monomial (g : N1)
    (i : Omega × bothAxesDomain.signedOrbits.toPairing.Orbit) :
    ∃ j, directSumRepresentation g (directSumBasis i) = directSumBasis j ∨
      directSumRepresentation g (directSumBasis i) = -directSumBasis j := by
  obtain ⟨j,hj⟩ := representation_monomial g i
  refine ⟨j,?_⟩
  change directSumRepresentation g (restriction (basis i)) = restriction (basis j) ∨
    directSumRepresentation g (restriction (basis i)) = -restriction (basis j)
  rw [← restriction_equivariant]
  rcases hj with hj | hj
  · exact Or.inl (congrArg restriction hj)
  · exact Or.inr ((congrArg restriction hj).trans (map_neg restriction _))

theorem directSumRepresentation_z : directSumRepresentation SpinAction.z = -1 := by
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := restriction.surjective v
  rw [← restriction_equivariant, representation_z]
  exact map_neg restriction w

theorem finrank_directSumSpace : Module.finrank ℝ DirectSumSpace = 98304 :=
  restriction.finrank_eq.symm.trans finrank_space

end TensorAction
end Sporadic.Monster.Construction.TrialitySpin
