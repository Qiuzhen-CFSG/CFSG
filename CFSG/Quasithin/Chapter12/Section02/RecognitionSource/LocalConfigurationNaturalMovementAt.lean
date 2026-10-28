module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceRank

/-!
# The H-star movement argument with ambient-local structural input

The weak-closure and TI-pair argument of 12.2.18 uses the structural theorem
only at the original G and T. Here it is carried through with that exact
local hypothesis. The rank bound still comes from the earlier H-star source
restrictions. No multiple-overgroup condition is needed for the implication
once an escaping H-star member has been supplied.

This preserves the universal APIs in LocalConfigurationPrefix and
LocalConfigurationNaturalMovement. The local versions feed the guarded
natural-action assembly, whose witness uses the same ambient G,T.
Source: Aschbacher–Smith 12.2.17–18, printed pp.800–801; B.6.8(4–5),
pp.113–115; I.6.2(1), pp.424–425.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

private theorem chosen_conjugates_in_sylow_centralize_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  let := D.elementary
  have hn := ((structural L h).2.2 V D).1
  have hi : (normalizer (V : Set G)).relIndex (T : Subgroup G) < Nat.card V := by
    rw [relIndex_eq_one.mpr hn]
    exact (Subgroup.one_lt_card_iff_ne_bot V).mpr D.ne_bot
  exact hTI.conjugate_le_centralizer_of_index V (T : Subgroup G)
    T.isPGroup' D.le_sylow hi g hg

private theorem chosen_weakClosure_zero_centralizes_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      0 < globalW V (T : Subgroup G) := by
  have hall := chosen_conjugates_in_sylow_centralize_at h D structural hTI
  constructor
  · apply le_inf (indexedWeakClosure_le V (T : Subgroup G) 0)
    rw [weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro A hA
    obtain ⟨g, rfl, hg⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
    exact hall g hg
  · apply bot_lt_iff_ne_bot.mpr
    intro he
    obtain ⟨g, hg, hn⟩ := (globalW_eq_zero_iff V (T : Subgroup G)).mp he
    exact hn (hall g hg)

private theorem chosen_sylow_centralizer_eq_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he := (D.fundamentalSetup h.toHypothesis1221).sylow_centralizer_module hu
  have ho : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl
      (((structural L h).2.2 V D).1)) (le_componentOrbit V T)
  rw [D.fundamentalSetup_module, ho] at he
  simpa only [Chapter3.Section02.localJoin, D.localOrbit_eq] using he

private theorem chosen_kernel_unique_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) =
      {normalizer (L : Set G)} := by
  rw [chosen_sylow_centralizer_eq_core_at h D structural]
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_unique
  ext N
  constructor
  · rintro ⟨hN, hle⟩
    exact Set.mem_singleton_iff.mpr (huniq N hN
      (((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))).trans hle))
  · intro he
    rw [Set.mem_singleton_iff] at he
    subst N
    exact ⟨hm, chosen_core_normalizer_le h D⟩

private theorem chosen_weakClosure_zero_local_control_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      (T : Subgroup G) ⊓ centralizer (V : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
        normalizer (L : Set G) := by
  let := D.elementary
  have hw := chosen_weakClosure_zero_centralizes_at h D structural hTI
  have hc := chosen_sylow_centralizer_eq_core_at h D structural
  refine ⟨hw.1.trans_eq hc, hc, ?_⟩
  exact SourceContainment.normalizer_weakClosure_zero_le
    ⟨D.ne_bot, D.le_sylow, ((structural L h).2.2 V D).1⟩ hw.2
    (chosen_kernel_unique_at h D structural)

/-- The first contradiction in 12.2.18: the weak closure cannot lie in
O₂(H) for an escaping H-star subgroup. -/
private theorem chosen_weakClosure_not_le_hstar_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ indexedWeakClosure V (T : Subgroup G) 0 ≤ H.pCoreIn 2 := by
  intro hw
  have he : indexedWeakClosure V (T : Subgroup G) 0 =
      indexedWeakClosure V (H.pCoreIn 2) 0 :=
    SubgroupFamily.span_eq_in_p_overgroup (conjugateCorankFamily_invariant V 0)
      T (H.pCoreIn 2) (isPGroup_pCoreIn 2 H) hw
  have hn : H ≤ normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) := by
    rw [he]
    exact (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))).trans
      (normalizer_le_weakClosure_normalizer V (H.pCoreIn 2) 0)
  exact hH.1.2 (hn.trans (chosen_weakClosure_zero_local_control_at h D structural hTI).2.2)

/-- Thus the original conjugacy family supplies an A=Vᵍ inside T whose
image in H/O₂(H) is nontrivial, as used in 12.2.18. -/
private theorem exists_chosen_conjugate_outside_hstar_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ H.pCoreIn 2 := by
  classical
  by_contra hn
  apply chosen_weakClosure_not_le_hstar_core_at h D structural hTI hH
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g, rfl, hg⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
  by_contra he
  exact hn ⟨g, hg, he⟩



theorem chosen_omega_centralizer_le_of_noEscape_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) :
    centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  have hi := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup V (T : Subgroup G)
    D.le_sylow T.isPGroup' (((structural L h).2.2 V D).1) D.ne_bot
  obtain ⟨v, hv, hv1⟩ := (V ⊓ omegaCenterIn (T : Subgroup G)).bot_or_exists_ne_one.resolve_left hi
  exact (centralizer_le (Set.singleton_subset_iff.mpr hv.2)).trans (hnone v hv.1 hv1)

private theorem chosen_hstar_residual_generation_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) (hAQ : ¬ A ≤ H.pCoreIn 2) :
    (pResidual 2 H).map H.subtype ≤ componentOrbit A H := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let S := T.subtype hTH
  have hp : ChapterB.IsMinimalParabolicOver S ⊤ :=
    chosen_hstar_minimalParabolic_at h D structural hTI hH
  let Y := (componentOrbit A H).subgroupOf H
  let : Y.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_componentOrbit A H)
  have hn : ¬ Y ≤ ChapterB.minimalParabolicCore S hp := by
    intro he
    apply hAQ
    intro a ha
    have hm : (⟨a, hTH (hAT ha)⟩ : H) ∈
        (S : Subgroup H) ⊓ ChapterB.minimalParabolicCore S hp :=
      ⟨hAT ha, he (le_componentOrbit A H ha)⟩
    rw [ChapterB.minimalParabolic_sylow_inf_core S hp] at hm
    exact mem_map_of_mem H.subtype hm
  have hKY := (ChapterB.minimalParabolic_normal_subgroup_residual_dichotomy S hp Y).resolve_left hn
  rintro _ ⟨a, ha, rfl⟩
  exact hKY ha

private theorem hstarRankControl_of_small_disjoint_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hsmall : ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
      IsElementaryAbelian 2 A → Disjoint A (H.pCoreIn 2) → Nat.card A ≤ 4) :
    HStarRankControl T V H := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  exact ⟨hQT.trans (((structural L h).2.2 V D).1), hsmall,
    chosen_hstar_residual_generation_at h D structural hTI hH⟩

private theorem hstarRankControl_of_quotient_rank_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hrank : primeRank 2 (H ⧸ pCore 2 H) ≤ 2) : HStarRankControl T V H := by
  apply hstarRankControl_of_small_disjoint_at h D structural hTI hH
  intro A hAT hA hd
  let := hA
  let i : A →* H := inclusion (hAT.trans hH.1.1.2)
  let f : A →* (H ⧸ pCore 2 H) := (QuotientGroup.mk' (pCore 2 H)).comp i
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply bot_unique
    intro a ha
    change a = 1
    apply Subtype.ext
    apply hd.le_bot
    refine ⟨a.property, ?_⟩
    exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff (i a)).mp ha)
  have hr := (Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans hrank
  rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) A]
  exact Nat.pow_le_pow_right (by decide) hr

/-- The TI-pair contradiction of 12.2.18, retaining all original subgroups. -/
private theorem chosen_movement_of_rank_control_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) (hlarge : 4 < Nat.card V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (control : HStarRankControl T V H) : ¬ V ≤ H.pCoreIn 2 := by
  intro hVQ
  let := D.elementary
  obtain ⟨g, hgT, hgQ⟩ := exists_chosen_conjugate_outside_hstar_core_at h D structural hTI hH
  let A := V.map (MulAut.conj g).toMonoidHom
  let Q := H.pCoreIn 2
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hQN : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hcard : Nat.card A = Nat.card V := card_map_of_injective (MulAut.conj g).injective
  have hmeet : A ⊓ Q ≠ ⊥ := by
    intro he
    have hh := control.small_disjoint A hgT (IsElementaryAbelian.map _)
      (disjoint_iff.mpr he)
    rw [hcard] at hh
    exact (not_lt_of_ge hh) hlarge
  have horbit : componentOrbit A H ≤ centralizer (V : Set G) := by
    apply iSup_le
    intro a
    let B := A.map (MulAut.conj (a : G)).toMonoidHom
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
    have hBti : IsTISubgroup B := (hTI.map_equiv (MulAut.conj g)).map_equiv (MulAut.conj (a : G))
    have hBcard : Nat.card B = Nat.card V :=
      (card_map_of_injective (MulAut.conj (a : G)).injective).trans hcard
    have hQeq : Q.map (MulAut.conj (a : G)).toMonoidHom = Q :=
      mem_normalizer_iff_map_conj_eq.mp (hQN a.property)
    have hBmeet : B ⊓ Q ≠ ⊥ := by
      intro he
      have hmap : (A ⊓ Q).map (MulAut.conj (a : G)).toMonoidHom = ⊥ := by
        rw [Subgroup.map_inf _ _ _ (MulAut.conj (a : G)).injective, hQeq]
        exact he
      exact hmeet ((map_eq_bot_iff_of_injective _ (MulAut.conj (a : G)).injective).mp hmap)
    have hBn : B ⊓ normalizer (V : Set G) ≠ ⊥ := by
      intro he
      exact hBmeet (bot_unique ((inf_le_inf_left B control.core_normalizes).trans_eq he))
    have hP : IsPGroup 2 (V ⊔ B : Subgroup G) := by
      apply (T.isPGroup'.map (MulAut.conj (a : G)).toMonoidHom).to_le
      apply sup_le
      · apply hVQ.trans
        change Q ≤ _
        calc
          Q = Q.map (MulAut.conj (a : G)).toMonoidHom := hQeq.symm
          _ ≤ (T : Subgroup G).map (MulAut.conj (a : G)).toMonoidHom := map_mono hQT
      · exact map_mono hgT
    change B ≤ centralizer (V : Set G)
    by_cases he : B = V
    · rw [he]
      exact le_centralizer_iff_isMulCommutative.mpr inferInstance
    · have hd : Disjoint B V := by
        have hcross : ∃ b : G, B = V.map (MulAut.conj b).toMonoidHom := by
          refine ⟨(a : G) * g, ?_⟩
          change (V.map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj (a : G)).toMonoidHom = _
          rw [map_map]
          congr 1
          ext x
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            mul_inv_rev, mul_assoc]
        obtain ⟨b, hb⟩ := hcross
        exact ((hTI.eq_or_disjoint_conjugate b).resolve_left (hb ▸ he)) |> (hb ▸ ·)
      exact (ti_pair_directProduct_of_isPGroup B V hd hBti hTI hBcard hBn
        (by rw [sup_comm]; exact hP)).1
  have hKM : (pResidual 2 H).map H.subtype ≤ normalizer (L : Set G) :=
    (control.residual_generation A hgT hgQ).trans
      (horbit.trans (chosen_centralizer_le_of_noEscape D hnone))
  have hgen : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (Subgroup.map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
    simpa only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
      ← MonoidHom.range_eq_map, range_subtype] using hh
  apply hH.1.2
  rw [← hgen]
  exact sup_le hKM (structural L h).1

/-- The source application needs only the outstanding bound on H/O₂(H).
The size of V, minimal parabolicity and residual generation are discharged. -/
theorem chosen_movement_of_quotient_rank_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hrank : primeRank 2 (H ⧸ pCore 2 H) ≤ 2) : ¬ V ≤ H.pCoreIn 2 :=
  chosen_movement_of_rank_control_at h D structural hnone hTI (chosen_card_gt_four h D) hH
    (hstarRankControl_of_quotient_rank_at h D structural hTI hH hrank)



end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
