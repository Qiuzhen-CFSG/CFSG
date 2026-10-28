module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Standing
public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The component alternative of the escaping-subgroup construction

A C-component outside the common normalizer moves Ω₁Z(T), hence is
faithful. Enlarge it to a maximal faithful local component. The common
centralizer normalizer excludes a nonquasisimple enlargement; the exact
invariance and rigidity clauses of 13.1.2 then identify the enlargement
with the original component and give relative normality in H.

For the 13.1.9 application, distinct C-components commute modulo their
two-cores. Equality with the component containing L_R is excluded by the
same 13.1.2 rigidity clause. Thus the component alternative satisfies the
actual commutator bound. Canonical starred membership and the earlier
13.1.2 clauses remain explicit; the odd-prime alternative is separate.
Source: Aschbacher--Smith 13.1.6 and 13.1.9, printed pp.868--869.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter12.Section02 ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Precisely the T-invariance and comparable-local rigidity assertions
of earlier 13.1.2, only in its maximal faithful quasisimple case. -/
def QuasisimpleRigidity (T : Sylow 2 G) : Prop :=
  ∀ K : Subgroup G, FaithfulMaximalLocal T K → IsQuasisimple (XiQuotient K) →
    (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ∀ B : Subgroup G, B ∈ Chapter1.L G (T : Subgroup G) → B ≤ K → B = K

/-- Movement and faithful membership use the actual centralizer containment;
there is no unguarded 3.1.8 parameter. -/
theorem component_outside_faithful
    (h : Hypothesis1311 T) {M H Y : Subgroup G}
    (hCZ : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M)
    (hH : H ∈ HOver G (T : Set G)) (hY : Y ∈ cComponentsIn H) (hout : ¬ Y ≤ M) :
    ⁅omegaOneCenterAmbient (T : Subgroup G),Y⁆ ≠ ⊥ ∧
      Y ∈ MainForward.faithfulLocalComponents T := by
  have hmove : ⁅omegaOneCenterAmbient (T : Subgroup G),Y⁆ ≠ ⊥ := by
    intro he
    rw [commutator_comm] at he
    exact hout ((commutator_eq_bot_iff_le_centralizer.mp he).trans hCZ)
  have hYL := ((lemma_1_2_6 T hH).1 hY).2
  have htype := (Terminal.local_component_and_orbit_signalizerType T
    (lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)) hYL).1
  refine ⟨hmove,(mem_faithfulLocalComponents_iff T Y).mpr ⟨hYL,htype,?_⟩⟩
  intro hz
  let B := Y.subgroupOf H
  let e : B ≃* Y := subgroupOfEquivOfLe hY.1
  have hm : B.map H.subtype = Y := map_subgroupOf_eq_of_le hY.1
  have hb : intrinsicSignalizerModule B = ⊥ := by
    apply map_injective (f := H.subtype) H.subtype_injective
    rw [← intrinsicSignalizerModule_map_of_injective H.subtype H.subtype_injective,
      hm,hz,Subgroup.map_bot]
  have hr : ⁅reducedTwoSubgroup H,B⁆ = ⊥ := bot_unique
    ((reduced_commutator_le_intrinsicModule B hY.2.subnormal
      (htype.2.1.of_surjective e.symm.toMonoidHom e.symm.surjective)).trans_eq hb)
  have hc := congrArg (Subgroup.map H.subtype) hr
  rw [map_commutator,hm,Subgroup.map_bot] at hc
  have hTH : (T : Subgroup G) ≤ H := hH.2
  have hi := sylow_omegaCenter_le_reduced (T.subtype hTH)
    (mem_He_iff.mp (lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH))
  change omegaOneCenterAmbient ((T.subtype hTH) : Subgroup H) ≤ reducedTwoSubgroup H at hi
  have hi := map_mono (f := H.subtype) hi
  rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hi
  exact hmove (bot_unique ((commutator_mono hi le_rfl).trans_eq hc))

/-- Every outside C-component has all the clauses of alternative (2) of
13.1.6. Normality is relative to H, not ambient G. -/
theorem escaping_component_of_stars
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    {L H Y : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hY : Y ∈ cComponentsIn H) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    IsQuasisimple (XiQuotient Y) ∧ (Y.subgroupOf H).Normal ∧
      ⁅omegaOneCenterAmbient (T : Subgroup G),Y⁆ ≠ ⊥ ∧ FaithfulMaximalLocal T Y := by
  have hcL := nonquasisimple_centralizer_unique_of_stars h hmany hs hL hn
  have hHT : H ∈ HOver G (T : Set G) := ⟨mem_H_of_isTwoLocal hH.1,hTH⟩
  obtain ⟨hmove,hf⟩ := component_outside_faithful h hcL.2.1 hHT hY hout
  have hy := (mem_faithfulLocalComponents_iff T Y).mp hf
  obtain ⟨K,hK,hYK⟩ := exists_mem_LStar_ge hy.1
  have hkf := (mem_faithfulLocalComponents_iff T K).mp
    (faithful_local_overgroup T (h.simpleQTKE.evenCharacteristic T) hf hK.1 hYK)
  have hk : FaithfulMaximalLocal T K := ⟨hK,hkf.2⟩
  have hq : IsQuasisimple (XiQuotient K) := by
    by_contra hkn
    have hcK := nonquasisimple_centralizer_unique_of_stars h hmany hs hk hkn
    have he := hcL.2.2 _ hcK.1 hcK.2.1
    exact hout ((hYK.trans K.le_normalizer).trans_eq he)
  have he : Y = K := (hrig K hk hq).2 Y hy.1 hYK
  subst K
  have hTY := (hrig Y hk hq).1
  have hyH : Y.subgroupOf H ∈ Chapter1.L H (T.subtype hTH : Subgroup H) :=
    (mem_LIn_iff_subgroupOf hTH hY.1).mp ⟨hY.1,hy.1⟩
  have hnH : (T.subtype hTH : Subgroup H) ≤ normalizer (Y.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hY.1]
    intro t ht
    exact hTY ht
  obtain ⟨B,⟨hB,hYB,hBN⟩,_⟩ := lemma_1_2_4_containment_normality_source
    (uniqueness_local_quotient_sqtk h.simpleQTKE hHT.1) (T.subtype hTH) hyH hnH
  have heB : Y.subgroupOf H = B := hY.2.eq_of_le hB hYB
  exact ⟨hq,heB.symm ▸ hBN,hmove,hk⟩

/-- The actual component case of the commutator claim on p.869.
The containing component cannot be the escaping component, since then
13.1.2(5) identifies it with the canonical supplement inside N_G(L). -/
theorem escaping_component_commutator
    (h : Hypothesis1311 T) (hrig : QuasisimpleRigidity T)
    {L H Y C : Subgroup G} (hH : H ∈ HOver G (T : Set G))
    (hY : Y ∈ cComponentsIn H) (hC : C ∈ cComponentsIn H)
    (hf : FaithfulMaximalLocal T Y) (hq : IsQuasisimple (XiQuotient Y))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (hA : canonicalSupplement T L ∈ Chapter1.L G (T : Subgroup G))
    (hAC : canonicalSupplement T L ≤ C) :
    ⁅Y,C⁆ ≤ Y.pCoreIn 2 := by
  have hne : Y ≠ C := by
    intro he
    have ha := (hrig Y hf hq).2 _ hA (hAC.trans_eq he.symm)
    exact hout (ha.symm.le.trans ((canonicalSupplement_le _ _).trans L.le_normalizer))
  have hneH : Y.subgroupOf H ≠ C.subgroupOf H := by
    intro he
    apply hne
    simpa only [map_subgroupOf_eq_of_le hY.1,map_subgroupOf_eq_of_le hC.1]
      using congrArg (map H.subtype) he
  have hc := (ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two
    (uniqueness_local_quotient_sqtk h.simpleQTKE hH.1) hY.2 hC.2 hneH).1.trans inf_le_left
  have hm := map_mono (f := H.subtype) hc
  rw [map_commutator,map_subgroupOf_eq_of_le hY.1,map_subgroupOf_eq_of_le hC.1,
    pCoreIn_subgroupOf 2 Y H hY.1,map_subgroupOf_eq_of_le ((pCoreIn_le 2 Y).trans hY.1)] at hm
  exact hm

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
