module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SU3.TernaryPerfectCover
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
/-!
# The literal five quotient models in 13.3.2(1)

The three-cover is specified by its actual cyclic center and alternating
central quotient. Counting the concrete carriers gives the five orders;
all five centers are cyclic. These are model facts, not a proof of the
preceding source classification.

Source: Aschbacher--Smith, Lemma 13.3.2(1), printed pp.884--885.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter1.Section02.LocalModels
universe u
variable {Q : Type u} [Group Q]
@[expose] def MidSizeModel (Q : Type u) [Group Q] : Prop :=
  IsAlternating Q 5 ∨ ClassicalGroup.IsPSL Q 3 2 ∨ IsAlternating Q 6 ∨
    IsAlternatingCover Q 6 ∨ ClassicalGroup.IsPSU Q 3 3

theorem MidSizeModel.card (h : MidSizeModel Q) :
    Nat.card Q = 60 ∨ Nat.card Q = 168 ∨ Nat.card Q = 360 ∨
      Nat.card Q = 1080 ∨ Nat.card Q = 6048 := by
  rcases h with ⟨⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨_,⟨z⟩,⟨e⟩⟩ |
    ⟨F,_,_,J,hF,hJ,⟨e⟩⟩
  · left; rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]; norm_num
  · right; left
    rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective, hF]
    norm_num
  · right; right; left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]; norm_num
  · right; right; right; left
    rw [card_eq_card_quotient_mul_card_subgroup (center Q),
      Nat.card_congr e.toEquiv, Nat.card_congr z.toEquiv, nat_card_alternatingGroup]
    norm_num
  · right; right; right; right
    exact (Nat.card_congr e.toEquiv).trans
      (BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.card_projective J hF hJ)

theorem MidSizeModel.center_cyclic [IsQuasisimple Q] (h : MidSizeModel Q) :
    IsCyclic (center Q) := by
  rcases h with ⟨⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨_,⟨z⟩,_⟩ |
    ⟨F,_,_,J,hF,hJ,⟨e⟩⟩
  · have hc : center (alternatingGroup (Fin 5)) = ⊥ :=
      alternatingGroup.center_eq_bot (by norm_num)
    let : IsCyclic (center (alternatingGroup (Fin 5))) := by rw [hc]; infer_instance
    exact isCyclic_of_injective (centerCongr e).toMonoidHom (centerCongr e).injective
  · have hc : center (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = ⊥ := by
      let := Atlas.sl_perfect (F := F) 3 (by decide)
      exact Group.IsPerfect.center_quotient_center_eq_bot _
    let : IsCyclic (center (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) := by
      rw [hc]; infer_instance
    exact isCyclic_of_injective (centerCongr e).toMonoidHom (centerCongr e).injective
  · have hc : center (alternatingGroup (Fin 6)) = ⊥ :=
      alternatingGroup.center_eq_bot (by norm_num)
    let : IsCyclic (center (alternatingGroup (Fin 6))) := by rw [hc]; infer_instance
    exact isCyclic_of_injective (centerCongr e).toMonoidHom (centerCongr e).injective
  · exact isCyclic_of_injective z.toMonoidHom z.injective
  · let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
      Atlas.G2.isSimple_commutator_binary
    let : IsSimpleGroup Q := (e.trans (J.projectiveEquivBinaryG2Derived hF hJ)).isSimpleGroup
    rw [center_eq_bot_of_simple_perfect]; infer_instance
end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
