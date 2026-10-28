module
public import Theory.Representation.BinaryAlternatingFiveExtension.OverlapFactorization
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.OverlapTwist

/-!
# Removing the marked overlap discrepancy in the ordinary unitary model

The affine restriction factorization applies to one marked plane equivalence.
Its translation module is the literal plane radical in the projective unitary
group. The proved central twist extends to the actual point endpoint and the
other factors extend to the actual plane endpoint. Transporting through both
commuting squares therefore removes every discrepancy preserving that module.

Source: Aschbacher--Smith 13.5.17, printed p.922, ordinary U₄(2) branch.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.OverlapRigidity
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation BinaryPermutation.AlternatingFiveExtension
local notation "hn" => Nat.le_refl 1
local notation "P" => pointParabolic 1 hn
local notation "R" => planeParabolic 1 hn
local notation "B" => overlap 1 hn
local notation "M" => ProjectiveGroup 1 hn
local notation "A" => AlternatingModel

theorem planeCore_eq : InvolutionPlacement.planeCore = (pCore 2 R).map (R).subtype := by
  rw [BinaryCompletion.plane_eq_local]
  rfl

theorem planeCore_mem (r : R) : (r:M)∈InvolutionPlacement.planeCore ↔ r∈pCore 2 R := by
  rw [planeCore_eq]
  exact mem_map_iff_mem (R).subtype_injective

theorem overlapEquiv_translations (E : A ≃* R)
    (hV : (SemidirectProduct.inl : V →* A).range.map E.toMonoidHom=pCore 2 R)
    (hB : borelEmbedding.range.map E.toMonoidHom=(B).subgroupOf R) (x : BorelModel) :
    ((OverlapTwist.overlapEquiv E hB x : B):M)∈InvolutionPlacement.planeCore ↔ x.right=1 := by
  rw [OverlapTwist.overlapEquiv_val,planeCore_mem,←hV,
    mem_map_equiv,E.symm_apply_apply,SemidirectProduct.range_inl_eq_ker_rightHom]
  change x.right.val=1 ↔ x.right=1
  constructor
  · exact fun h => Subtype.ext h
  · intro h
    rw [h]
    rfl

def affineIso (E : A ≃* R)
    (hB : borelEmbedding.range.map E.toMonoidHom=(B).subgroupOf R) :
    Iso (⟨OverlapTwist.pointEmbedding E hB,borelEmbedding⟩ : RankTwoAmalgam P BorelModel A)
      (amalgam 1 hn) where
  left := MulEquiv.refl P
  middle := OverlapTwist.overlapEquiv E hB
  right := E
  left_commutes _ := rfl
  right_commutes x := (OverlapTwist.plane_compatible E hB x).symm

theorem factorsThrough_marked (δ : MulAut B)
    (hδ : ∀ b : B, (b:M)∈InvolutionPlacement.planeCore →
      ((δ b : B):M)∈InvolutionPlacement.planeCore) :
    FactorsThrough (amalgam 1 hn) δ := by
  obtain ⟨E,hz,hV,hB,_⟩ := OverlapTwist.exists_marked_plane_equiv_with_twist
  let eB := OverlapTwist.overlapEquiv E hB
  let α : MulAut BorelModel := MulAut.congr eB.symm δ
  have hN (x : BorelModel) (hx : x.right=1) : (α x).right=1 := by
    apply (overlapEquiv_translations E hV hB (α x)).mp
    have he : eB (α x)=δ (eB x) := by
      simp [α,MulAut.congr_apply]
    rw [he]
    exact hδ _ ((overlapEquiv_translations E hV hB x).mpr hx)
  have hf := OverlapFactorization.factorsThrough_of_preserves_translations
    (OverlapTwist.pointEmbedding E hB) (OverlapTwist.borelTwist_extends_point E hz hB) α hN
  have hft := (affineIso E hB).factorsThrough_iff α |>.mp hf
  have he : MulAut.congr eB α=δ := by
    apply MulEquiv.ext
    intro b
    simp [α,MulAut.congr_apply]
  exact he ▸ hft
end CFSG.Quasithin.ChapterF.UnitaryTwo.OverlapRigidity
