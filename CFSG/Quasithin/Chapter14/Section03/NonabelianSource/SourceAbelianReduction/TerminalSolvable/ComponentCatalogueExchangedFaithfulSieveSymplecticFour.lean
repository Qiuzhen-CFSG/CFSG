module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveSelfDual
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank.SourceBound
public import Theory.SpecificGroups.SymplecticFour.Binary
public import Theory.Representation.SymplecticFourOrthogonalCover.Universal
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import Theory.Representation.CentralCoverSelfDualFlag

/-!
# All derived symplectic-four images in the exchanged branch

For n≥2 the sharp automorphism bound places the actual faithful action in
the completed small-module classification, which recognizes its natural
self-dual action. At n=1 the derived group is A₆. Its complete binary
catalogue and degree bound leave its two natural four-spaces, both of
which preserve the duad-module pairing. Every positive exponent is excluded.

Source: Aschbacher--Smith G.9.3(9), G.11.6, printed pp.354,366.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups MonoidAlgebra
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

private def alternating_six_first_selfDual :
    BinaryAlternatingSix.firstAlternating.Equiv BinaryAlternatingSix.firstAlternating.dual := by
  apply Representation.BinaryCoverSocle.selfDualOfPairing
    BinaryAlternatingSix.firstAlternating Theory.SpecificGroups.SymmetricSix.polarForm
  · apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro w hw
    exact Theory.SpecificGroups.SymmetricSix.polarForm_nondegenerate.1 w
      (fun v => LinearMap.congr_fun hw v)
  · intro a w z
    have hh := Theory.SpecificGroups.SymmetricSix.polarAction_form a.val w
      (BinaryAlternatingSix.firstAlternating a⁻¹ z)
    change Theory.SpecificGroups.SymmetricSix.polarForm
      (BinaryAlternatingSix.firstAlternating a w)
      (BinaryAlternatingSix.firstAlternating a (BinaryAlternatingSix.firstAlternating a⁻¹ z)) =
      Theory.SpecificGroups.SymmetricSix.polarForm w
        (BinaryAlternatingSix.firstAlternating a⁻¹ z) at hh
    rw [Representation.self_inv_apply] at hh
    exact hh

namespace ExchangedFaithfulSource
attribute [local instance] ZMod.algebra
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)
  {K : Type*} [Field K] [Finite K] [CharP K 2]

include s

/-- Every genuine derived symplectic natural row is self-dual for the same H. -/
theorem image_not_symplectic_four_natural [Algebra (ZMod 2) K]
    (hq : ChapterG.Section09.Quasiequivalent
      (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)
      (ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.binaryNatural K)) :
    False := by
  apply s.image_not_selfDual
  apply ExchangedAction.selfDual_of_quasiequivalent hq
  refine .mk (SymplecticFourOrthogonalCover.binarySelfDual (K := K)) ?_
  intro a
  apply LinearMap.ext
  intro w
  exact SymplecticFourOrthogonalCover.binarySelfDual_equivariant a w

/-- Nonbinary symplectic recognition is invoked on the literal faithful H
representation; its conclusion is then excluded by same-action self-duality. -/
theorem image_not_nonbinary_symplectic_four {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n)
    (e : s.image (componentOrbit L ⊤) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) K)) : False := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let H := s.image (componentOrbit L ⊤)
  let σ := (s.imageAction.comp H.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (s.imageAction.comp H.subtype)).mpr s.image_irreducible
  have hf : Function.Injective σ :=
    s.image_setup.faithful.comp (H.subtype_injective.comp e.symm.injective)
  have hu := s.image_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derived_automorphism_rank_le hK hn
  change primeRank 2 (MulAut (commutator (Matrix.symplecticGroup (Fin 2) K))) ≤ 3 * n at hr
  have hd : finrank (ZMod 2) I ≤ 6 * n + 2 := by omega
  have hq := ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.small_quasiequivalent
    hn hK hf hd
  exact s.image_not_symplectic_four_natural
    (ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.quasiequivalent_of_comp_equiv e hq)

/-- The complete binary A₆ catalogue leaves only its two natural four-spaces
in the sharp exchanged range. Both are self-dual for the actual H-action. -/
theorem image_not_alternating_six
    (e : s.image (componentOrbit L ⊤) ≃* alternatingGroup (Fin 6)) : False := by
  let H := s.image (componentOrbit L ⊤)
  let σ := (s.imageAction.comp H.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (s.imageAction.comp H.subtype)).mpr s.image_irreducible
  have hu := s.image_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.alternating_six_automorphism_two_rank
  have hd : finrank (ZMod 2) I ≤ 5 := by omega
  rcases BinaryAlternatingSix.alternating_classify σ with h | h | h | h <;> obtain ⟨a⟩ := h
  · have hh := a.toLinearEquiv.finrank_eq
    have hp := s.dimension_gt_two
    simp only [Module.finrank_self] at hh
    omega
  · apply s.image_not_selfDual
    apply ExchangedAction.selfDual_of_quasiequivalent (σ := BinaryAlternatingSix.firstAlternating) _
      alternating_six_first_selfDual
    refine ⟨e,a.toLinearEquiv,?_⟩
    intro x w
    have hh := LinearMap.congr_fun (a.toIntertwiningMap.isIntertwining' (e x)) w
    change a.toLinearEquiv (s.imageAction (H.subtype (e.symm (e x))) w) =
      BinaryAlternatingSix.firstAlternating (e x) (a.toLinearEquiv w) at hh
    change a.toLinearEquiv (s.imageAction (H.subtype x) w) =
      BinaryAlternatingSix.firstAlternating (e x) (a.toLinearEquiv w)
    simpa only [MulEquiv.symm_apply_apply] using hh
  · apply s.image_not_selfDual
    apply ExchangedAction.selfDual_of_quasiequivalent (σ := BinaryAlternatingSix.firstAlternating) _
      alternating_six_first_selfDual
    refine ⟨e.trans BinaryAlternatingSix.alternatingDiagramAut,a.toLinearEquiv,?_⟩
    intro x w
    have hh := LinearMap.congr_fun (a.toIntertwiningMap.isIntertwining' (e x)) w
    change a.toLinearEquiv (s.imageAction (H.subtype (e.symm (e x))) w) =
      BinaryAlternatingSix.firstAlternating (BinaryAlternatingSix.alternatingDiagramAut (e x))
        (a.toLinearEquiv w) at hh
    change a.toLinearEquiv (s.imageAction (H.subtype x) w) =
      BinaryAlternatingSix.firstAlternating (BinaryAlternatingSix.alternatingDiagramAut (e x))
        (a.toLinearEquiv w)
    simpa only [MulEquiv.symm_apply_apply] using hh
  · have hh := a.toLinearEquiv.finrank_eq.trans BinaryAlternatingSix.tensor_finrank
    omega

omit [CharP K 2] in
/-- The binary endpoint of the derived symplectic family is the actual A₆. -/
theorem image_not_binary_symplectic_four (hK : Nat.card K = 2)
    (e : s.image (componentOrbit L ⊤) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) K)) : False :=
  s.image_not_alternating_six
    (e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hK))

/-- Every positive binary exponent of the derived symplectic-four family
is excluded, without a supplied module-recognition conclusion. -/
theorem image_not_symplectic_four {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = 2 ^ n)
    (e : s.image (componentOrbit L ⊤) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) K)) : False := by
  by_cases hn1 : n = 1
  · exact s.image_not_binary_symplectic_four (by simpa [hn1] using hK) e
  · exact s.image_not_nonbinary_symplectic_four (by omega) hK e


end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
