module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerRanks
public import Theory.GroupTheory.CentralSectionNormalComplement

/-!
# The normal three-complement in the original centralizer product

For C = C_N(K/O₂(K)), the central preimage L₁ lies in C. Every three-Sylow
of C R₁ lies in C because the quotient by C is a two-group; the previously
proved three-rank bound therefore makes it cyclic. The literal point-action
kernel gives [L₁,C R₁] ≤ O₂(L₁), and L₁/O₂(L₁) has order three.
Burnside transfer supplies a normal three-complement in C R₁.

All subgroups and quotient maps belong to the original group and flag.
No normality of C R₁ in N_G(K) is used or asserted.
Source: Aschbacher–Smith 14.7.21(1), printed p.1049, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The central preimage L₁ acts trivially on the original residual quotient. -/
theorem extraspecial_point_le_residualCentralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    F.Li L 1 ≤ normalizerResidualCentralizer F := by
  intro a ha
  let k : K F := ⟨a,pointResidual_le F ha⟩
  have hz : QuotientGroup.mk' (pCore 2 (K F)) k ∈ center _ := by
    change k ∈ (center _).comap (QuotientGroup.mk' (pCore 2 (K F)))
    rw [←extraspecial_point_eq_central_preimage h hab structural previous faithful he]
    exact ha
  refine ⟨⟨a,(K F).le_normalizer k.property⟩,?_,rfl⟩
  change pCoreNormalizerAction 2 (K F) ⟨k,(K F).le_normalizer k.property⟩ = 1
  rw [pCoreNormalizerAction_on_component]
  apply MulEquiv.ext
  intro x
  change QuotientGroup.mk' (pCore 2 (K F)) k * x * _ = x
  rw [←(mem_center_iff.mp hz x),mul_assoc,mul_inv_cancel,mul_one]

omit [Finite G] in
/-- The literal residual kernel is normal in its full normalizer. -/
theorem normalizerResidualCentralizer_normalizes :
    normalizer (K F : Set G) ≤ normalizer (normalizerResidualCentralizer F : Set G) := by
  let N := normalizer (K F : Set G)
  have hn : ((normalizerResidualCentralizer F).subgroupOf N).Normal := by
    change (((pCoreNormalizerAction 2 (K F)).ker.map N.subtype).comap N.subtype).Normal
    rw [comap_map_eq_self_of_injective N.subtype_injective]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp hn

/-- A three-Sylow of C_K R₁ is cyclic, with its literal containment in C_K. -/
theorem extraspecial_centralizer_point_sylow_cyclic
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (S : Sylow 3 (normalizerResidualCentralizer F ⊔ F.Ri L 1 : Subgroup G)) :
    (S : Subgroup _).map (normalizerResidualCentralizer F ⊔ F.Ri L 1).subtype ≤
      normalizerResidualCentralizer F ∧ IsCyclic S := by
  let C := normalizerResidualCentralizer F
  let R := F.Ri L 1
  let D := C ⊔ R
  have hRY := (isSylowIn_iff.mp (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hDY : D ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he) hRY
  let C' := C.subgroupOf D
  let R' := R.subgroupOf D
  have hDC : D ≤ normalizer (C : Set G) :=
    (hDY.trans inf_le_left).trans normalizerResidualCentralizer_normalizes
  let : C'.Normal := normal_subgroupOf_of_le_normalizer hDC
  have hgen : C' ⊔ R' = ⊤ := by
    rw [←subgroupOf_sup (show C ≤ D from le_sup_left) (show R ≤ D from le_sup_right)]
    exact subgroupOf_self D
  have hidx : ¬ 3 ∣ C'.index := by
    have hi : C'.index ∣ Nat.card R' := by
      rw [←relIndex_top_right (H := C'),←hgen,relIndex_sup_left]
      exact relIndex_dvd_card _ _
    have hR2 : IsPGroup 2 R' :=
      (isPGroup_pCoreIn 2 _).of_equiv (subgroupOfEquivOfLe (show R ≤ D from le_sup_right)).symm
    obtain ⟨k,hk⟩ := hR2.exists_card_eq
    intro hh
    have hh' : 3 ∣ 2^k := hk ▸ hh.trans hi
    exact ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mp
      ((by decide : Nat.Coprime 3 2).pow_right k)) hh'
  have hSC : (S : Subgroup D) ≤ C' := by
    rw [←relIndex_eq_one]
    obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
    have hcop : Nat.Coprime C'.index (Nat.card S) := hk ▸
      ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr hidx).symm.pow_right k
    exact Nat.eq_one_of_dvd_coprimes hcop (C'.relIndex_dvd_index_of_normal _)
      (relIndex_dvd_card _ _)
  refine ⟨?_,?_⟩
  · rintro x ⟨s,hs,rfl⟩
    exact hSC hs
  · have hr : primeRank 3 C' ≤ 1 := by
      rw [primeRank_congr 3 (subgroupOfEquivOfLe (show C ≤ D from le_sup_left))]
      exact (extraspecial_normalizer_threeRanks d h hab structural previous faithful he).2
    have hc : IsCyclic (S.subtype hSC) :=
      (S.subtype hSC).isCyclic_of_odd_of_primeRank_le_one (by decide) hr
    exact (subgroupOfEquivOfLe hSC).isCyclic.mp hc

/-- Burnside's normal three-complement conclusion for the actual C_K R₁. -/
theorem extraspecial_centralizer_point_normal_complement
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    HasNormalPComplement 3 (normalizerResidualCentralizer F ⊔ F.Ri L 1 : Subgroup G) := by
  let C := normalizerResidualCentralizer F
  let R := F.Ri L 1
  let D := C ⊔ R
  let A := F.Li L 1
  let Q := A.pCoreIn 2
  have hAD : A ≤ D :=
    (extraspecial_point_le_residualCentralizer h hab structural previous faithful he).trans le_sup_left
  have hDY : D ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he)
    (isSylowIn_iff.mp (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hDA : D ≤ normalizer (A : Set G) := (hDY.trans inf_le_left).trans
    (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)
  let : (A.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer hDA
  have hpA : 3 ∣ Nat.card (A.subgroupOf D) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv]
    exact (pointResidual_core_quotient_card h structural).symm ▸
      (pCore 2 A).index_dvd_card
  have hpQ : Nat.Coprime 3 (Nat.card (Q.subgroupOf D)) := by
    have hQ2 : IsPGroup 2 (Q.subgroupOf D) := (isPGroup_pCoreIn 2 A).of_equiv
      (subgroupOfEquivOfLe ((pCoreIn_le 2 A).trans hAD)).symm
    obtain ⟨k,hk⟩ := hQ2.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hcomm : ⁅A,D⁆ ≤ Q := by
    apply commutator_le_core_of_pCoreNormalizerAction_eq_one 2 A D hDA
    intro x
    obtain ⟨a,ha,heq⟩ := (hDY x.property).2
    exact (show a = inclusion hDA x from Subtype.ext heq) ▸ ha
  have hcomm' : ⁅A.subgroupOf D,(⊤ : Subgroup D)⁆ ≤ Q.subgroupOf D := by
    apply (map_le_map_iff_of_injective D.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hAD,←MonoidHom.range_eq_map,D.range_subtype,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 A).trans hAD)]
    exact hcomm
  obtain ⟨S⟩ := Sylow.nonempty (p := 3) (G := D)
  let := (extraspecial_centralizer_point_sylow_cyclic d h hab structural previous faithful he S).2
  exact S.hasNormalPComplement_of_cyclic_of_central_section
    (A.subgroupOf D) (Q.subgroupOf D) hpA hpQ hcomm'

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
