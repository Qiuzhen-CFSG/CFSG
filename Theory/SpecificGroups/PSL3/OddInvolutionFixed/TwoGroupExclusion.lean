module

public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.CharacteristicTwo
public import Theory.GroupTheory.CubicCentralKernelSL2

/-!
# An odd PSL₃ involution never has a two-group centralizer

The actual centralizer is a cubic central quotient of GL₂. Its determinant
kernel SL₂ survives injectively, including over the field of order three.
The odd root subgroup in this SL₂ rules out a two-group centralizer.

Source: Aschbacher--Smith A.3.21(a), printed p.55, and the one-involution
centralizer inspection in G.4.1, printed p.342.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.OddInvolutionFixed
open Theory.GroupTheory
variable {F : Type*} [Field F] [Finite F]
theorem involution_centralizer_not_twoGroup
    (hodd : Odd (Nat.card F)) (h2 : (2:F)≠0)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    ¬ IsPGroup 2 (centralizer ({t} : Set PSL(3,F))) := by
  obtain ⟨f, _, hk, hcube⟩ := exists_gl2_cubic_central_surjection t ht h2
  let D := (GeneralLinearGroup.det (n := Fin 2) (R := F)).ker
  let e : D ≃* SL(2,F) := (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm
  let j := ((D.map f).subtype.comp (f.subgroupMap D)).comp e.symm.toMonoidHom
  have hj : Function.Injective j :=
    Subtype.val_injective.comp ((injective_sl2_of_cubic_central_kernel f hk hcube D e).comp e.symm.injective)
  exact not_twoGroup_of_sl2_odd_embedding hodd j hj
end Matrix.PSL3.OddInvolutionFixed
