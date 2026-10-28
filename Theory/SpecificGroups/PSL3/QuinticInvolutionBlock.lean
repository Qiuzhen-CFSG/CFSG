module

public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.CharacteristicTwo
public import Theory.SpecificGroups.SL2.CubicCentralDerived

/-!
# The characteristic SL₂ block of a PSL₃ involution centralizer

The block is the literal commutator subgroup of the supplied involution
centralizer. It is SL₂ over the same field and its centralizer is the center.
Thus the block is preserved by every automorphism preserving the supplied
involution; a subgroup centralizing the block normalizes every subgroup of
this involution centralizer.

Source: Aschbacher--Smith 6.1.4, printed p.666.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.TwoFiveSylow

private theorem gl2_commutator_equiv {F : Type*} [Field F] [Finite F]
    (hlarge : 3 < Nat.card F) : Nonempty (commutator (GL (Fin 2) F) ≃* SL(2,F)) := by
  let D := (GeneralLinearGroup.det (n := Fin 2) (R := F)).ker
  let e : SL(2,F) ≃* D := SpecialLinearGroup.determinantKernelEquiv (Fin 2) F
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hd : commutator (GL (Fin 2) F) = D := by
    apply le_antisymm (Abelianization.commutator_subset_ker _)
    exact (commutator_eq_self (H := D)).ge.trans (commutator_mono le_top le_top)
  exact ⟨(MulEquiv.subgroupCongr hd).trans e.symm⟩

/-- The actual characteristic derived block and its exact centralizer,
with no choice of an unrelated isomorphic SL₂ subgroup. -/
theorem involution_centralizer_commutator_structure
    {F : Type*} [Field F] [Finite F] (hlarge : 3 < Nat.card F) (h2 : (2:F) ≠ 0)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    Nonempty (commutator (centralizer ({t} : Set PSL(3,F))) ≃* SL(2,F)) ∧
      centralizer (commutator (centralizer ({t} : Set PSL(3,F))) :
        Set (centralizer ({t} : Set PSL(3,F)))) =
        center (centralizer ({t} : Set PSL(3,F))) := by
  obtain ⟨f,hf,hk,hcube⟩ := OddInvolutionFixed.exists_gl2_cubic_central_surjection t ht h2
  obtain ⟨e⟩ := gl2_commutator_equiv hlarge
  exact SpecialLinearGroup.commutator_structure_of_cubic_central_matrix_surjection
    (MonoidHom.id _) Function.injective_id e hlarge f hf hk hcube

end Matrix.PSL3.TwoFiveSylow
