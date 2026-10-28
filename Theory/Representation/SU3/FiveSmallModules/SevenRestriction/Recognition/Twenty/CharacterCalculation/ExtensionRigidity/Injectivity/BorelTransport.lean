module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.RealizationInputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison

/-!
# Transporting the marked Bruhat coefficients along a Borel equivalence

Both coefficients of each Bruhat summand belong to the literal Borel.
A Borel equivalence therefore transports their matrices by changing basis.
The proved degree-twenty Borel comparison applies this to any reference model
with zero root-center invariants and trivial SU-center action. No whole-SU
equivalence or Weyl comparison is used.

Source: the coefficient formulas in Huppert II.10.12 and the extraspecial-root
comparison proved in `CharacterCalculation.BorelComparison`.
-/

@[expose] public section
open Module Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity
variable {F : Type*} [Field F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

private theorem matrix_change_basis (b : Basis (Fin 20) K W)
    (e : V ≃ₗ[K] W) (X : Module.End K V) (Y : Module.End K W)
    (h : ∀ v, e (X v) = Y (e v)) :
    LinearMap.toMatrixAlgEquiv (b.map e.symm) X = LinearMap.toMatrixAlgEquiv b Y := by
  ext i j
  simp only [LinearMap.toMatrixAlgEquiv_apply, Basis.map_apply, Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_symm]
  rw [h, e.apply_symm_apply]

/-- The actual coefficient basis transports using only a Borel equivalence. -/
noncomputable def Coordinates.ofBorelEquiv
    (ρ : Representation K J.specialSubgroup V) (σ : Representation K J.specialSubgroup W)
    (e : Representation.Equiv (ρ.comp (specialBorel J hJ).subtype)
      (σ.comp (specialBorel J hJ).subtype)) (C : Coordinates J hJ σ) :
    Coordinates J hJ ρ where
  basis := C.basis.map e.toLinearEquiv.symm
  point := C.point
  centerEquiv := C.centerEquiv
  left_eq s c := by
    rw [← C.left_eq s c]
    apply matrix_change_basis
    intro v
    unfold leftCoefficient
    split_ifs with hz
    · simp
    · exact congr($(e.toIntertwiningMap.2
        ⟨_, mul_mem (mem_sup_left ⟨_, rfl⟩) (mem_sup_right ⟨_, rfl⟩)⟩) v)
  right_eq s c := by
    rw [← C.right_eq s c]
    apply matrix_change_basis
    intro v
    unfold rightCoefficient
    split_ifs with hz
    · simp
    · exact congr($(e.toIntertwiningMap.2 ⟨_, mem_sup_left ⟨_, rfl⟩⟩) v)

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
open Degrees.RootEigenline
universe v

/-- A genuine reference action is enough; the arbitrary input action is
compared only on the Borel, over its original coefficient field. -/
theorem twenty_bruhat_coordinates_of_reference_models
    (hmodels : TwentyBruhatReferenceModels.{v}) : TwentyBruhatCoordinates.{v} := by
  intro F _ _ J hc hconj K _ _ _ U _ _ _ ρ hdim hcenter hfix
  obtain ⟨M⟩ := hmodels F J hc hconj K
  obtain ⟨e⟩ := twenty_borel_comparison F J hc hconj K U (Fin 20 → K)
    ρ M.representation hdim (by simp) hcenter M.center_le_ker hfix M.rootCenter_invariants
  exact ⟨ExtensionRigidity.Injectivity.Coordinates.ofBorelEquiv
    (FormTransport.standardForm J) rfl ρ M.representation e M.coordinates⟩

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
