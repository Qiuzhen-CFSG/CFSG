module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.OverlapRigidityExtension
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ExtendedAffinePlane
/-!
# Compatible correction on the whole doubled plane

Transport the affine inner correction through the same marked ordinary and
extended plane comparisons. Its actor fixes the long root, so conjugation
preserves the entire extended overlap. The resulting plane automorphism
extends the ordinary correction on the literal binary plane inclusion.

This is the compatibility input used to assemble the doubled normal A₅
source amalgam in Aschbacher--Smith 13.5.17, printed p.922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.OverlapRigidityFull
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation BinaryPermutation.AlternatingFiveExtension
open OverlapFactorizationExtension
local notation "hn" => Nat.le_refl 1
local notation "R" => planeParabolic 1 hn
local notation "B" => overlap 1 hn
local notation "M" => ProjectiveGroup 1 hn
local notation "ER" => Extension.plane 1 hn
local notation "EB" => Subgroup.subgroupOf (Extension.overlap 1 hn) (Extension.plane 1 hn)
local notation "A" => AlternatingModel
local notation "Z" => SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)
/-- Remove the ordinary overlap discrepancy with a compatible automorphism
of the full plane, preserving its entire overlap. -/
theorem iso_with_full_extension (E : A ≃* R)
    (hz : E (Z : A)=ModelClasses.longRight)
    (hV : (SemidirectProduct.inl : V →* A).range.map E.toMonoidHom=pCore 2 R)
    (hB : borelEmbedding.range.map E.toMonoidHom= (B).subgroupOf (R))
    (F : SymmetricModel ≃* ER)
    (hFz : F (Z : SymmetricModel)=ExtendedAffinePlane.longRight)
    (hFE : ∀ x : A, F (symmetricEmbedding x)=Extension.binaryPlaneInclusion (E x))
    (δ : MulAut B)
    (hδ : ∀ b : B, (b:M)∈InvolutionPlacement.planeCore →
      ((δ b : B):M)∈InvolutionPlacement.planeCore) :
    ∃ e : Iso (twistRight (amalgam 1 hn) δ) (amalgam 1 hn),
      ∃ f : MulAut ER, (EB).map f.toMonoidHom=EB ∧
      ∀ x : R, f (Extension.binaryPlaneInclusion x)=Extension.binaryPlaneInclusion (e.right x) := by
  obtain ⟨e,a,ha,he⟩ := OverlapRigidityExtension.iso_with_inner_extension E hz hV hB δ hδ
  have hfix : MulAut.conj (F a) ExtendedAffinePlane.longRight=ExtendedAffinePlane.longRight := by
    have hh := congrArg F (conj_marked_root a ha)
    simpa only [MulAut.conj_apply,map_mul,map_inv,hFz] using hh
  have haB : F a ∈ EB := by
    rw [← ExtendedAffinePlane.right_long_centralizer,mem_centralizer_singleton_iff]
    simpa only [MulAut.conj_apply,mul_inv_eq_iff_eq_mul] using hfix
  refine ⟨e,MulAut.conj (F a),mem_normalizer_iff_map_conj_eq.mp ((EB).le_normalizer haB),?_⟩
  intro x
  have hh := congrArg F (he x)
  rw [hFE,E.apply_symm_apply] at hh
  change Extension.binaryPlaneInclusion (e.right x) = F (a * symmetricEmbedding (E.symm x) * a⁻¹) at hh
  rw [map_mul,map_mul,map_inv,hFE,E.apply_symm_apply] at hh
  exact hh.symm
end CFSG.Quasithin.ChapterF.UnitaryTwo.OverlapRigidityFull
