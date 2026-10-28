module
public import Theory.Representation.BinaryAlternatingFiveExtension.OverlapFactorizationExtension
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.OverlapRigidity

/-!
# Extendable correction of the literal unitary overlap

The ordinary unitary overlap correction can be chosen so that its plane
component extends to the full affine S₅ plane. This extension is conjugation
by an element fixing the marked root. The two literal unitary inclusion
squares and the affine inclusion square remain part of the conclusion.

This discharges the extendability of the plane correction when assembling
the doubled normal A₅ amalgam of Aschbacher--Smith 13.5.17, printed p.922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.OverlapRigidityExtension
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation BinaryPermutation.AlternatingFiveExtension
open OverlapFactorizationExtension
local notation "hn" => Nat.le_refl 1
local notation "R" => planeParabolic 1 hn
local notation "B" => overlap 1 hn
local notation "M" => ProjectiveGroup 1 hn
local notation "A" => AlternatingModel
local notation "Z" => SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)

/-- Literal unitary overlap correction with a compatible full affine extension. -/
theorem iso_with_inner_extension (E : A ≃* R)
    (hz : E (Z : A)=ModelClasses.longRight)
    (hV : (SemidirectProduct.inl : V →* A).range.map E.toMonoidHom=pCore 2 R)
    (hB : borelEmbedding.range.map E.toMonoidHom=(B).subgroupOf R)
    (δ : MulAut B)
    (hδ : ∀ b : B, (b:M)∈InvolutionPlacement.planeCore →
      ((δ b : B):M)∈InvolutionPlacement.planeCore) :
    ∃ e : Iso (twistRight (amalgam 1 hn) δ) (amalgam 1 hn),
      ∃ a : SymmetricModel, a.right 4=4 ∧
        ∀ x : R, symmetricEmbedding (E.symm (e.right x)) =
          MulAut.conj a (symmetricEmbedding (E.symm x)) := by
  let f := OverlapRigidity.affineIso E hB
  let α : MulAut BorelModel := MulAut.congr f.middle.symm δ
  have hN (x : BorelModel) (hx : x.right=1) : (α x).right=1 := by
    apply (OverlapRigidity.overlapEquiv_translations E hV hB (α x)).mp
    have he : f.middle (α x)=δ (f.middle x) := by
      simp [α,MulAut.congr_apply]
    change (f.middle (α x) : M)∈InvolutionPlacement.planeCore
    rw [he]
    exact hδ _ ((OverlapRigidity.overlapEquiv_translations E hV hB x).mpr hx)
  obtain ⟨e,a,ha,he⟩ := OverlapFactorizationExtension.iso_with_inner_extension
    (OverlapTwist.pointEmbedding E hB) (OverlapTwist.borelTwist_extends_point E hz hB) α hN
  have hα : MulAut.congr f.middle α=δ := by
    ext b
    simp [α,MulAut.congr_apply]
  have hw : ∀ δ' : MulAut B, MulAut.congr f.middle α=δ' →
      ∃ e' : Iso (twistRight (amalgam 1 hn) δ') (amalgam 1 hn),
        ∃ a : SymmetricModel, a.right 4=4 ∧
          ∀ x : R, symmetricEmbedding (E.symm (e'.right x)) =
            MulAut.conj a (symmetricEmbedding (E.symm x)) := by
    intro δ' hδ'
    subst δ'
    refine ⟨(f.twistRight α).symm.trans (e.trans f),a,ha,?_⟩
    intro x
    change symmetricEmbedding (E.symm (E (e.right (E.symm x)))) = _
    rw [E.symm_apply_apply]
    exact he (E.symm x)
  exact hw δ hα
end CFSG.Quasithin.ChapterF.UnitaryTwo.OverlapRigidityExtension
