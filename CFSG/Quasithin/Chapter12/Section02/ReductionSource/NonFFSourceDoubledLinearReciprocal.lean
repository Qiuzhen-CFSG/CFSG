module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearC28
public import Theory.SpecificGroups.SL3.BinaryOddRankOne
public import Theory.GroupTheory.CComponent.OddRankNormal

/-!
# The original nonbinary linear-three reciprocal source

If the reciprocal Fitting image did not escape, the actual component would
be a nonnormal C-component. Its two-core quotient would be centerless.
The original SL3 seed image then identifies that whole quotient with SL3.
The split diagonal torus supplies an odd prime of rank at least two, forcing
normality in the SQTK ambient group and contradicting reciprocal index two.
The same witness supplies C.2.8 on the whole natural-dual orbit, using only
two-subgroup section-centralizer control and retaining all scalar centers.

Source: Aschbacher--Smith A.3.8(3),4.2.5–8,C.2.8 and7.3.4,
printed pp.46,609–610,147,699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem quotient_marking_of_centerless
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (hz : center (L ⧸ pCore 2 L) = ⊥) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := by
  let := h.quasisimple
  let m := hmodel.some
  let r := m.groupEquiv.toMonoidHom.comp D.componentQuotientHom
  have hr : Function.Surjective r := m.groupEquiv.surjective.comp D.componentQuotientHom_surjective
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :=
    m.groupEquiv.symm.toEquiv.nontrivial
  have hk : r.ker ≤ center (L ⧸ pCore 2 L) := by
    rw [←IsQuasisimple.comap_center_of_surjective r hr]
    exact comap_mono bot_le
  have hi : Function.Injective r := (MonoidHom.ker_eq_bot_iff r).mp
    (le_bot_iff.mp (hz ▸ hk))
  exact ⟨MulEquiv.ofBijective r ⟨hi,hr⟩⟩

/-- Every genuine nonbinary linear-three reciprocal witness has Fitting escape. -/
theorem sourceOrbit_linear_reciprocal_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    EscapeCase L V A := by
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (by simpa only [←D.sourceOrbit_eq] using
      D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))
  have hM := D.doubledNormalizer_unique h
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  obtain ⟨J,H,W,hw,hh⟩ := reciprocal_case_of_not_unique h.toHypothesis1221 D hu
    A hc.1 hc.2 ho ((hA.trans inf_le_right).trans
      (centralizer_le (by rw [D.sourceOrbit_eq]; exact le_componentOrbit V T))) hnot
  refine ⟨J,H,W,hw,?_⟩
  intro hf
  have hd := hh hf
  have hz := reciprocal_coreQuotient_center_eq_bot hw.2.2.2.2.2.2.1.sqtk hd
  obtain ⟨e⟩ := D.quotient_marking_of_centerless h F hmodel hz
  have hex : ∃ p : ℕ, p.Prime ∧ Odd p ∧
      2 ≤ primeRank p (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := by
    by_contra! hh
    have he := Matrix.SL3.BinaryOddRankOne.degree_eq_one_of_odd_primeRanks_le_one
      F.Carrier F.degree_pos F.card_eq (fun p hp ho => by have := hh p hp ho; omega)
    omega
  obtain ⟨p,hp,hpo,hr⟩ := hex
  let : Fact p.Prime := ⟨hp⟩
  have hLH : L ≤ H := hd.1 ▸ (map_subtype_le _).trans inf_le_right
  let e₀ := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hLH))
  let := h.quasisimple
  let : IsQuasisimple ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv e₀.symm
  have hz₀ : center ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) = ⊥ := by
    apply (eq_bot_iff_card _).mpr
    rw [Nat.card_congr (centerCongr e₀).toEquiv,hz]
    exact Nat.card_unique
  have hr₀ : 2 ≤ primeRank p ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) := by
    rwa [primeRank_congr p (e₀.trans e)]
  let : (L.subgroupOf H).Normal := hd.2.1.normal_of_coprime_core_center_primeRank hpo
    (by rw [hz₀]; simp) hr₀ (hw.2.2.2.2.2.2.1.sqtk.stronglyQuasithin p hp hpo)
  have hi := hd.2.2.2.1
  have hnorm := hd.2.2.1
  rw [normalizer_eq_top] at hnorm
  rw [←hnorm,index_top] at hi
  norm_num at hi

private theorem linear_witness_core_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H U : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hw : Witness L V A J H U) :
    D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L := by
  obtain ⟨hc,_,hW,hne⟩ := D.doubledOrbit_oddActorResidual_cover h A
    (by simpa only [←D.sourceOrbit_eq] using hA) ho
  have hI := ((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer
  obtain ⟨hs,_⟩ := coveringOvergroup_eta L.le_normalizer le_rfl hI hc.subset hne
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hNL : (L.subgroupOf (normalizer (L : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  have hperfect : IsPPerfect 2 L := by
    intro N hN hp
    let := hN
    have he : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hp.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  refine ⟨?_,core_le_sectionCentralizer_of_eta
    L.le_normalizer hNL hperfect hs.1 hw.1.1.1⟩
  rw [D.sourceOrbit_eq]
  exact hW.trans hw.2.1.1

/-- The same original odd actor produces full-orbit C.2.8 and reciprocal escape. -/
theorem sourceOrbit_linear_reciprocal_hypothesisC28
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H U : Subgroup G, Witness L V A J H U ∧
      D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
        (H ⊓ normalizer (L : Set G))
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
        (J.pCoreIn 2) D.sourceOrbit ∧
      ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
        (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H := by
  have hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) :=
    le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  obtain ⟨J,H,U,hw,hescape⟩ := D.sourceOrbit_linear_reciprocal_escape h F hn hmodel A hA ho hnot
  obtain ⟨hWJ,hJC⟩ := D.linear_witness_core_data h hA ho hw
  exact ⟨J,H,U,hw,hWJ,hJC,D.sourceOrbit_linear_witness_hypothesisC28 h hd F hmodel hw hWJ hJC,hescape⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
