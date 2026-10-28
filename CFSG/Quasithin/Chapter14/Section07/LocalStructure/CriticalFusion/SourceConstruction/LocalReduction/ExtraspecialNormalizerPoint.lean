module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSixteenExclusion
/-!
# The point residual inside the maximal normalizer

The actual point image is the center of the star residual. Because
O₂(L₁) = O₂(K), it lifts to the full preimage of Z(K/O₂(K)) in K.
Consequently L₁ is characteristic in K, so N_G(K) normalizes L₁.
The maximal-local normalizer theorem and the nontrivial common two-core
then identify N_G(O₂(K)) = N_G(L₁) = N_G(K).

These are original-group inputs to the maximal-normalizer argument of
Aschbacher–Smith 14.7.21(1), printed pp.1049–1050, refs/quasithin.pdf.
No equality N_G(K) = H or final residual classification is asserted.
Every earlier source premise is retained for its existing assembly owner.
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

/-- L₁ is exactly the full central preimage in the original K/O₂(K). -/
theorem extraspecial_point_eq_central_preimage
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (F.Li L 1).subgroupOf (K F) =
      (center ((K F) ⧸ pCore 2 (K F))).comap (QuotientGroup.mk' (pCore 2 (K F))) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hs := point_star_eq_center_of_extraspecial_residual h hab structural previous hex hcard hexp
  let A := (F.Li L 1).subgroupOf (K F)
  let q := QuotientGroup.mk' (pCore 2 (K F))
  let P := pResidual 2 (HStar F.H)
  let eK := residualStarEquiv F
  have himage : (A.map q).map eK.toMonoidHom = center P := by
    apply le_antisymm
    · rintro x ⟨y,⟨a,ha,rfl⟩,rfl⟩
      have hm : (eK (q a) : HStar F.H) ∈ star F (F.Li L 1) := by
        rw [residualStarEquiv_mk]
        exact mem_map_of_mem (starMap F) ha
      rw [hs] at hm
      obtain ⟨z,hz,hzx⟩ := hm
      exact (Subtype.ext hzx : z = eK (q a)) ▸ hz
    · intro x hx
      have hm : (x : HStar F.H) ∈ star F (F.Li L 1) := by
        rw [hs]
        exact mem_map_of_mem P.subtype hx
      obtain ⟨a,ha,haq⟩ := hm
      let k : K F := ⟨a,pointResidual_le F ha⟩
      refine ⟨q k,mem_map_of_mem q ha,?_⟩
      apply Subtype.ext
      change (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H) = x
      rw [residualStarEquiv_mk]
      exact haq
  have himageq : A.map q = center ((K F) ⧸ pCore 2 (K F)) := by
    apply map_injective (f := eK.toMonoidHom) eK.injective
    rw [himage]
    exact (Subgroup.center_map_equiv eK).symm
  have hker : q.ker ≤ A := by
    rw [QuotientGroup.ker_mk']
    intro k hk
    have hkP : (k : G) ∈ (K F).pCoreIn 2 := mem_map_of_mem (K F).subtype hk
    have hP : (F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2 :=
      (extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful ⟨e⟩).1
    exact pCoreIn_le 2 (F.Li L 1) (hP.symm ▸ hkP)
  have hh := congrArg (Subgroup.comap q) himageq
  simpa only [comap_map_eq,sup_eq_left.mpr hker] using hh

/-- The point residual is characteristic in K, hence normal in its full normalizer. -/
theorem extraspecial_point_characteristic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((F.Li L 1).subgroupOf (K F)).Characteristic := by
  rw [extraspecial_point_eq_central_preimage h hab structural previous faithful he]
  exact Characteristic.comap_quotient_mk inferInstance

/-- The literal N_G(K) normalizes L₁ and its two-core. -/
theorem extraspecial_normalizer_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer (K F : Set G) ≤ normalizer (F.Li L 1 : Set G) := by
  let := extraspecial_point_characteristic h hab structural previous faithful he
  simpa only [map_subgroupOf_eq_of_le (pointResidual_le F)] using
    normalizer_le_normalizer_characteristic_image (K F) ((F.Li L 1).subgroupOf (K F))

/-- The full residual, point residual and their common two-core have the
same maximal-local normalizer. -/
theorem extraspecial_core_normalizer_eq
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer ((K F).pCoreIn 2 : Set G) = normalizer (K F : Set G) ∧
      normalizer (F.Li L 1 : Set G) = normalizer (K F : Set G) := by
  have hX := extraspecial_residual_mem_Xi h hab structural previous faithful he
  have hcore : (K F).pCoreIn 2 ≠ ⊥ := hX.pCoreIn_ne_bot
    (fun _ hM _ hN hNM hn => lemma_1_1_3_1 hM hN hNM hn)
    (lemma_1_1_4_6 T (d.qtke.evenCharacteristic T))
  have hmax := (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1
  have hNP : normalizer (K F : Set G) ≤ normalizer ((K F).pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F))
  have heq : normalizer ((K F).pCoreIn 2 : Set G) = normalizer (K F : Set G) :=
    (hmax.eq_of_le ⟨(K F).pCoreIn 2,hcore,isPGroup_pCoreIn 2 (K F),rfl⟩ hNP).symm
  refine ⟨heq,le_antisymm ?_ (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)⟩
  have hP := (extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he).1
  rw [←heq,←hP]
  exact normalizer_le_normalizer_characteristic_image (F.Li L 1) (pCore 2 (F.Li L 1))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
