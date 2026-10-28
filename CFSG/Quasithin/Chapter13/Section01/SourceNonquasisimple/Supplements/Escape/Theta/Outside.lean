module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Theta.Cover
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NonquasisimpleFitting
public import Theory.GroupTheory.MaximalTwoLocalCore

/-!
# The intersection contradiction for the theta construction

If a theta preimage in H lies in M=N_G(L), A.4.4 identifies O₂(H)
with the core of H∩M. It is then radical in M and its characteristic
normalizers lie in H∩M. The proved three-free instance of C.2.6 puts
O₂,F(L), and hence every supported canonical radical, in H. This contradicts
the standing uniqueness of the maximal overgroup of Ξ_p(L)T.

The canonical starred premise is owned by qt-d-1314-canonical-radical-star;
qt-d-1317-source must discharge it in the final source theorem.
Source: Aschbacher--Smith 13.1.6 and (+), printed p.868.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Theta
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterG.Section08 ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem local_radical_threeFree (h : Hypothesis1311 T) {L : Subgroup G}
    (hL : L ∈ Chapter1.L G (T : Subgroup G)) (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ¬ 3 ∣ Nat.card (solvableRadical L) := by
  let J := L ⊔ (T : Subgroup G)
  let B := L.subgroupOf J
  let e : B ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  have hnB : ¬ IsQuasisimple (B ⧸ pCore 2 B) := by
    intro hB
    let := hB
    exact hn (IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)))
  have hB := ChapterA.Section03.cComponent_radical_primeTo_three_of_not_quasisimple
    (RadicalExclusions.sqtk_of_mem_H h.simpleQTKE hL.2.2) hL.1 hnB
  have he := Nat.card_congr
    ((solvableRadical B).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  rw [map_solvableRadical_equiv e] at he
  exact he ▸ hB

private theorem xiP_le_fittingPreimage {p : ℕ} [Fact p.Prime] (L : Subgroup G) :
    XiP p L ≤ (twoFittingCore L).map L.subtype := by
  apply map_mono
  apply (map_subtype_le (pResidual 2 (xiPPreimage p L))).trans
  apply comap_mono
  exact (map_subtype_le _).trans (pCore_le_fitting (XiQuotient L) p)

omit [Finite G] in
private theorem intersection_radical {H M : Subgroup G}
    (hH : IsMaximalTwoLocal H) (hRM : H.pCoreIn 2 ≤ M)
    (hcore : H.pCoreIn 2 = (H ⊓ M).pCoreIn 2) :
    IsPRadical 2 ((H.pCoreIn 2).subgroupOf M) := by
  refine ⟨?_,?_⟩
  · intro he
    apply maximalTwoLocal_core_ne_bot hH
    simpa only [map_subgroupOf_eq_of_le hRM,Subgroup.map_bot] using congrArg (map M.subtype) he
  · apply map_injective M.subtype_injective
    change ((normalizer ((H.pCoreIn 2).subgroupOf M : Set M)).pCoreIn 2).map M.subtype = _
    rw [map_pCoreIn_of_injective 2 _ M.subtype M.subtype_injective,
      ← subgroupOf_normalizer_eq hRM,maximalTwoLocal_normalizer_core hH,
      subgroupOf_map_subtype,← hcore,map_subgroupOf_eq_of_le hRM]

/-- Every actual theta preimage escapes the canonical maximal normalizer.
Only the authorized canonical starred membership remains an earlier premise. -/
theorem preimage_outside_of_stars (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    {θ : Subgroup (XiQuotient H)} (hθ : IsThetaSubgroup θ) :
    ¬ preimage H θ ≤ normalizer (L : Set G) := by
  intro hθM
  let M := normalizer (L : Set G)
  let R := H.pCoreIn 2
  have hf : L ∈ nonquasisimpleFaithful T :=
    ⟨(Adequate.mem_faithfulLocalComponents_iff T L).mpr ⟨hL.1.1,hL.2⟩,hn⟩
  obtain ⟨K,hK,hLK,_,_,_,_,_,p,hp,ho,_,hd,_⟩ := h.maximal_counterexample_of_many hmany hf
  have he : K = L := hL.1.2 K hK.1 hLK
  subst K
  let : Fact p.Prime := ⟨hp⟩
  have hstand := canonical_standing_of_star h hmany hL hn ho hd (hs L hL hn p hp ho hd)
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hstand.2.2.1
  have hRM : R ≤ M := (core_le_preimage H θ).trans hθM
  have hcore : R = (H ⊓ M).pCoreIn 2 := lemma_A_4_4_1 H M (preimage H θ)
    (core_le_preimage H θ) (le_inf (preimage_le H θ) hθM)
    (by rw [preimage_image]; exact Or.inl hθ)
  have hr := intersection_radical hH hRM hcore
  have hcontrol : (R.subgroupOf M).characteristicNormalizerClosure ≤ H.subgroupOf M :=
    characteristicNormalizerClosure_subgroupOf_le hRM
      (maximalTwoLocal_characteristicNormalizer_core hH).le
  have hLM : L ≤ M := L.le_normalizer
  let B := L.subgroupOf M
  let e : B ≃* L := subgroupOfEquivOfLe hLM
  let : B.Normal := normal_subgroupOf_of_le_normalizer (show M ≤ normalizer (L : Set G) from le_rfl)
  have hfitL : generalizedFitting L = pCore 2 L :=
    RadicalExclusions.component_fitting_of_global_He
      (lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T))
      ⟨hL.1.1.2.2,show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right⟩ ⟨le_sup_left,hL.1.1.1⟩
  have hfitB : generalizedFitting B = pCore 2 B := by
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfitL)
  have hthreeB : ¬ 3 ∣ Nat.card (solvableRadical B) := by
    have he := Nat.card_congr
      ((solvableRadical B).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    rw [map_solvableRadical_equiv e] at he
    exact he.symm ▸ local_radical_threeFree h hL.1.1 hn
  have hfit := ChapterC.Section02Source.fittingCore_le_of_normal_threeFree_radical
    (h.simpleQTKE.twoLocal_sqtk hstand.2.1.1) B (R.subgroupOf M) (H.subgroupOf M)
    hfitB hthreeB hr hcontrol
  have hFH : (twoFittingCore L).map L.subtype ≤ H := by
    rintro _ ⟨l,hl,rfl⟩
    have heL : e.symm l ∈ twoFittingCore B :=
      twoFittingCore_map_equiv_le e.symm (mem_map_of_mem _ hl)
    exact hfit (mem_map_of_mem B.subtype heL)
  exact hne (hstand.2.2.2.1 H hH
    (sup_le ((xiP_le_fittingPreimage L).trans hFH) hTH))

/-- The entire odd theta branch of 13.1.6, with its source inputs constructed. -/
theorem odd_witness_of_components_inside (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hcomp : ∀ C ∈ cComponentsIn H, C ≤ normalizer (L : Set G)) :
    ∃ Y : Subgroup G, Witness T L H Y ∧ OddShape Y := by
  obtain ⟨θ,hθ⟩ := exists_thetaSubgroup (pCore_quotient_pCore_eq_bot 2 (G := H))
  have hstand := nonquasisimple_centralizer_unique_of_stars h hmany hs hL hn
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hcore : H.pCoreIn 2 ≤ normalizer (L : Set G) := by
    have ht := pCoreIn_le_sylow H (T.subtype hTH)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at ht
    exact ht.trans hTL
  exact witness_of_preimage_outside hθ hcore hcomp hstand.2.1
    (preimage_outside_of_stars h hmany hs hL hn hH hTH hne hθ)

/-- Original 13.1.6 in the maximal nonquasisimple context used by 13.1.9.
The earlier 13.1.2 rigidity and canonical starred membership remain explicit. -/
theorem witness_exists_of_stars (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G)) :
    ∃ Y : Subgroup G, Witness T L H Y := by
  by_cases hcomp : ∀ C ∈ cComponentsIn H, C ≤ normalizer (L : Set G)
  · obtain ⟨Y,hY,_⟩ := odd_witness_of_components_inside h hmany hs hL hn hH hTH hne hcomp
    exact ⟨Y,hY⟩
  · push Not at hcomp
    obtain ⟨Y,hY,hout⟩ := hcomp
    exact ⟨Y,witness_of_outside_component h hmany hs hrig hL hn hH hTH hY hout⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Theta
