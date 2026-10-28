module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairCore
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.ResidualLift

/-!
# Lifting the original M24 pair residual

The quotient cover gives equality of the embedded two-residuals. Its
normalization by the original Sylow subgroup then normalizes the pair and
its two-core. The pair's two elementary core factors give normalization
of VA, while H-star minimality identifies the set product IT with H.
Every quotient, conjugator, subgroup inclusion and Sylow placement is
transported through the original H.

The actual chosen-module consumer is NonFFSourceMathieuM24Normalization,
which discharges the quotient cover. Source: Aschbacher--Smith 8.2.9(1--2),
printed p.720, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
open ChapterE Chapter8.Section02.HermitianSource Chapter8.Section02.Normalizer
open Chapter8.Section02.Normalizer.ParabolicReduction
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
  {i : I} {S : Sylow 2 I}
set_option backward.isDefEq.respectTransparency false

/-- Lift the literal cover for a selected degree-two pair. Both residuals
are embedded in the original ambient group, and H=IT is a set product. -/
theorem selected_normalization_of_quotient_cover
    (s : Selected H T M V I 2 i S)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hcover : pResidual 2 (H ⧸ pCore 2 H) ≤
      (I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :
    (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
      (T : Subgroup G) ≤ normalizer (I : Set G) ∧
      (H : Set G) = (I : Set G) * (T : Set G) ∧
      (T : Subgroup G) ≤ normalizer
        ((V ⊔ (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) : Subgroup G) : Set G) := by
  have hIH := s.family.le_ambient
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hVH := hVI.trans hIH
  let R := T.subtype hH.1.1.2
  let j : H := ⟨i.val,hIH i.property⟩
  have hTV' : (R : Subgroup H) ≤ normalizer (V.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hVH]
    exact comap_mono hTV
  have hgen : V.subgroupOf H ⊔ (V.subgroupOf H).map (MulAut.conj j⁻¹).toMonoidHom =
      I.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hIH,map_map]
    have hc : H.subtype.comp (MulAut.conj j⁻¹).toMonoidHom =
        (MulAut.conj i.val⁻¹).toMonoidHom.comp H.subtype := rfl
    rw [hc,←map_map,map_subgroupOf_eq_of_le hVH,s.generate]
  have hr := residual_eq_of_quotient_cover R (V.subgroupOf H) (I.subgroupOf H) j
    hTV' hgen hcover
  have hres : (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype := by
    have hh := congrArg (Subgroup.map H.subtype) hr
    let e : I.subgroupOf H ≃* I := subgroupOfEquivOfLe hIH
    have hc : H.subtype.comp (I.subgroupOf H).subtype = I.subtype.comp e.toMonoidHom := rfl
    rw [map_map,hc,←map_map,map_pResidual_of_surjective _ _ e.surjective] at hh
    exact hh
  have hTR : (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) := by
    rw [hres]
    exact hH.1.1.2.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pResidual 2 H)))
  have hP := (selected_two_core_product s).symm
  rw [sup_comm] at hP
  obtain ⟨hTI,hTA⟩ := offender_product_normalized I V _ (T : Subgroup G)
    i.val i.property s.generate hTV hTR hP
  refine ⟨hres,hTR,hTI,?_,hTA⟩
  change (H : Set G) = (I : Set G) * ((T : Subgroup G) : Set G)
  rw [←coe_mul_of_right_le_normalizer_left I (T : Subgroup G) hTI,
    selected_generates_hstar s hH]

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
