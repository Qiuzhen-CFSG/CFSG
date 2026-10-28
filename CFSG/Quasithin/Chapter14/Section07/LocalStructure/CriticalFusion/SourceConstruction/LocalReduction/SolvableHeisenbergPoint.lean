module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergNormalizer
public import Theory.GroupTheory.PResidual.ExtraspecialCubicCharacteristic

/-!
# Point normality from the proper local Heisenberg residual

The actual L₁ is a normal two-perfect subgroup of the selected local
residual R, with cubic intrinsic two-core quotient. Its image in R/O₂(R)
is therefore the center, and L₁ is characteristic in R. The complete
intrinsic embedding theorem already makes R normal in every two-local
overgroup of the selected local. Hence these overgroups normalize L₁.

The original solvability hypothesis produces such a local witness and
therefore proves relative normality of L₁ in the full point normalizer.
The literal quotient maps and the potentially proper local R are retained;
this does not identify R with O²(H) or complete the solvable exclusion.

Source: Aschbacher–Smith, 14.7.15(1,3), and 14.7.27–29,
printed pp.1047,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original point residual is characteristic in the proper local residual,
so its relative normality extends to every actual two-local overgroup. -/
theorem local_solvable_heisenberg_point_normal_in_twoLocal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3))
    (M : Subgroup G) (hM : IsTwoLocal M) (hIM : I ≤ M) :
    ((F.Li L 1).subgroupOf M).Normal := by
  let R := (pResidual 2 I).map I.subtype
  let A := (F.Li L 1).subgroupOf R
  have hp : IsPPerfect 2 (F.Li L 1) := isPPerfect_embedded_pResidual 2 _
  have hAR : F.Li L 1 ≤ R := by
    have hh := embedded_pResidual_mono 2 (F.Li_one_le_of_mem_Hz hI)
    rwa [(pResidual_eq_top_iff 2 (F.Li L 1)).mpr hp,
      ←MonoidHom.range_eq_map,range_subtype] at hh
  let := hn
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    ((map_subtype_le _).trans (F.normalizes_Li_one_of_relative_normal hI))
  let eR := (pResidual 2 I).equivMapOfInjective I.subtype I.subtype_injective
  let eStar := (coreQuotientEquivImage 2 (pResidual 2 I)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)))
  let e := (QuotientGroup.congr _ _ eR.symm (pCore_map_iso 2 eR.symm)).trans
    (eStar.trans he.some)
  let : IsExtraspecial 3 (R ⧸ pCore 2 R) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  let eA : A ≃* F.Li L 1 := subgroupOfEquivOfLe hAR
  let : A.Characteristic := characteristic_of_normal_twoPerfect_cubic A
    (hp.of_surjective eA.symm.toMonoidHom eA.symm.surjective)
    ((Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv).trans
      (pointResidual_core_quotient_card h structural))
  have hRn := local_solvable_heisenberg_normal_in_twoLocal h hab structural previous faithful
    I hI hs hn he M hM hIM
  have hMR : M ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans hIM)).mp hRn
  apply (normal_subgroupOf_iff_le_normalizer ((F.Li_one_le_of_mem_Hz hI).trans hIM)).mpr
  have hnorm := hMR.trans (normalizer_le_normalizer_characteristic_image R A)
  simpa only [A,map_subgroupOf_eq_of_le hAR] using hnorm

/-- Under the original solvability assumption, L₁ is normal in the full point
normalizer. The proof uses the actual proper local lift and discharges its
irreducibility and intrinsic embedding premises. -/
theorem original_solvable_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H) :
    ((F.Li L 1).subgroupOf F.H).Normal := by
  obtain ⟨I,hIH,hI,hIs,_,hn,_,_,he,_⟩ :=
    local_solvable_minimal_heisenberg_residual h hab structural previous faithful F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) hs
  let e := (coreQuotientEquivImage 2 (pResidual 2 I)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)))
  have heStar : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3) :=
    ⟨e.symm.trans he.some⟩
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro hz
    have hc := F.card 1 (by decide)
    rw [hz,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  exact local_solvable_heisenberg_point_normal_in_twoLocal h hab structural previous faithful
    I hI hIs hn heStar F.H hH hIH

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
