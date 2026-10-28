module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Alternatives
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# The odd escaping commutator in the canonical supplement geometry

The canonical supplement is faithful. Faithfulness ascends to the component
containing it. If that component were nonquasisimple, 13.1.4 would identify
its overgroup with the common centralizer overgroup, a contradiction.
Its image modulo O₂(H) is therefore an ordinary component. That image
centralizes the image of the solvable normal odd witness; lifting back
gives the bound by the witness's own two-core.

This uses the faithful canonical-supplement premise already supplied by
the source's first paragraph, rather than a separate rank-two commutator
calculation. Canonical geometry remains with qt-d-1317-supplements;
canonical stars remain with qt-d-1314-canonical-radical-star and are
discharged by qt-d-1317-source in final assembly.
Source: Aschbacher--Smith 13.1.9, printed pp.869--870.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The odd witness is solvable through its literal two-core quotient. -/
theorem OddShape.solvable {Y : Subgroup G} (hY : OddShape Y) : Group.IsSolvable Y := by
  obtain ⟨_,d,hd,_,hp,_,_⟩ := hY
  let : Fact d.Prime := ⟨hd⟩
  let : Group.IsNilpotent (XiQuotient Y) := hp.isNilpotent
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 Y)).mpr
    ⟨inferInstance,inferInstance⟩

/-- A faithful local in a distinct overgroup can only lie in a component
with quasisimple two-core quotient. This uses the genuine uniqueness
conclusion of 13.1.4 at that containing component. -/
theorem containing_component_quasisimple_of_stars
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) {L H A C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hA : A ∈ MainForward.faithfulLocalComponents T)
    (hC : C ∈ cComponentsIn H) (hAC : A ≤ C) : IsQuasisimple (XiQuotient C) := by
  have hHT : H ∈ HOver G (T : Set G) := ⟨mem_H_of_isTwoLocal hH.1,hTH⟩
  have hcL : C ∈ Chapter1.L G (T : Subgroup G) := ((lemma_1_2_6 T hHT).1 hC).2
  have hfC := faithful_local_overgroup T (h.simpleQTKE.evenCharacteristic T) hA hcL hAC
  by_contra hnC
  obtain ⟨K,_,_,hfK,hKn,_,_,hu,_⟩ :=
    h.maximal_counterexample_of_many hmany ⟨hfC,hnC⟩
  have hK := nonquasisimple_centralizer_unique_of_stars h hmany hs hfK hKn.2
  have hL := nonquasisimple_centralizer_unique_of_stars h hmany hs hL hn
  exact hne ((hu H hH (sup_le hC.1 hTH)).trans (hL.2.2 _ hK.1 hK.2.1))

/-- Solvable normal subgroups commute with a quasisimple C-component modulo
their own two-cores, with the normality interpreted inside H. -/
theorem solvable_normal_component_commutator {H Y C : Subgroup G}
    (hYH : Y ≤ H) (hYn : (Y.subgroupOf H).Normal) (hYs : Group.IsSolvable Y)
    (hC : C ∈ cComponentsIn H) (hq : IsQuasisimple (XiQuotient C)) :
    ⁅Y,C⁆ ≤ Y.pCoreIn 2 := by
  let B := C.subgroupOf H
  let D := Y.subgroupOf H
  let e : B ≃* C := subgroupOfEquivOfLe hC.1
  let eY : D ≃* Y := subgroupOfEquivOfLe hYH
  let q := QuotientGroup.mk' (pCore 2 H)
  let : D.Normal := hYn
  let : Group.IsSolvable Y := hYs
  let : Group.IsSolvable D := Group.isSolvable_of_surjective
    (f := eY.symm.toMonoidHom) eY.symm.surjective
  let : (D.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (D.map q) := Group.isSolvable_of_surjective (q.subgroupMap_surjective D)
  let : IsQuasisimple (XiQuotient C) := hq
  let eqv : XiQuotient C ≃* B.map q :=
    (QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans
      (cComponentTwoCoreQuotientEquiv hC.2)
  have hcomp : IsComponent (XiQuotient H) (B.map q) :=
    ⟨hC.2.subnormal.map (QuotientGroup.mk'_surjective _),IsQuasisimple.of_mulEquiv eqv⟩
  have hc : ⁅D.map q,B.map q⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hcomp.le_centralizer_of_solvable_normal (D.map q))
  have hcore : ⁅D,B⁆ ≤ pCore 2 H := by
    rwa [← map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at hc
  have hcG := map_mono (f := H.subtype) hcore
  rw [map_commutator,map_subgroupOf_eq_of_le hYH,map_subgroupOf_eq_of_le hC.1] at hcG
  have hCY : C ≤ normalizer (Y : Set G) := hC.1.trans
    ((normal_subgroupOf_iff_le_normalizer hYH).mp hYn)
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hCY) hcG).trans
    (inf_pCoreIn_le_of_le 2 hYH)

/-- The odd case of the commutator claim, using the actual faithful L_R. -/
theorem odd_witness_commutator
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) {L H Y C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G)) (w : Witness T L H Y) (ho : OddShape Y)
    (hA : canonicalSupplement T L ∈ MainForward.faithfulLocalComponents T)
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement T L ≤ C) :
    ⁅Y,C⁆ ≤ Y.pCoreIn 2 :=
  solvable_normal_component_commutator w.le_overgroup w.normal ho.solvable hC
    (containing_component_quasisimple_of_stars h hmany hs hL hn hH hTH hne hA hC hAC)

/-- Both escaping alternatives satisfy the canonical normalization and Sylow
conclusions in the first paragraph of p.870. The geometry is literal. -/
theorem witness_canonical_geometry
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T) {L H Y C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G)) (w : Witness T L H Y)
    (hA : canonicalSupplement T L ∈ MainForward.faithfulLocalComponents T)
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement T L ≤ C)
    (hTA : (T : Subgroup G) ≤ normalizer (canonicalSupplement T L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 = radicalSylowCentralizer T L)
    (hcent : radicalSylowCentralizer T (canonicalSupplement T L) = radicalSylowCentralizer T L) :
    ⁅Y,C⁆ ≤ Y.pCoreIn 2 ∧ Y ≤ normalizer (canonicalSupplement T L : Set G) ∧
      Y.pCoreIn 2 ≤ radicalSylowCentralizer T L ∧
      IsSylowIn 2 (radicalSylowCentralizer T L) (Y ⊔ radicalSylowCentralizer T L) := by
  have hc : ⁅Y,C⁆ ≤ Y.pCoreIn 2 := by
    rcases w.alternatives with ho | ⟨hY,hq,hf⟩
    · exact odd_witness_commutator h hmany hs hL hn hH hTH hne w ho hA hC hAC
    · exact escaping_component_commutator h hrig ⟨mem_H_of_isTwoLocal hH.1,hTH⟩
        hY hC hf hq w.outside ((mem_faithfulLocalComponents_iff T _).mp hA).1 hAC
  exact ⟨hc,sylow_join_of_canonical_centralizer hTH w.le_overgroup w.normal hAC hC.1
    hTA hcore hcent hc⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
