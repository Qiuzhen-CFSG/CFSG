module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationPrefix
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalPreparation
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The movement deduction in 12.2.18

The original chosen module has order greater than four. A two-rank bound on
H/O₂(H) therefore forces a nontrivial intersection of O₂(H) with the conjugate
of V supplied by 12.2.17. If V itself lay in O₂(H), the elementary TI-pair
argument would make every H-conjugate of that subgroup centralize V.

The normal-subgroup dichotomy for the original minimal parabolic puts O²(H)
in their join. Together with T this is H, contradicting H's escape from N_G(L).
Minimal parabolicity and residual generation are proved here using 12.2.17;
normality of O₂(H) is used only inside H. No multiple-overgroup assumption is
introduced. The existence of H, its quotient rank bound, and the nonsolvable
exclusion remain separate source obligations.

Source: Aschbacher--Smith, 12.2.18, printed pp.800--801; B.6.8(4--5),
printed pp.113--115; I.6.2(1), printed pp.424--425.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- Intermediate inputs for the rank argument, with the original core and residual.
`hstarRankControl_of_quotient_rank` discharges the normalization and generation
fields; only the two-rank bound must be supplied by the earlier local analysis. -/
structure HStarRankControl (T : Sylow 2 G) (V H : Subgroup G) : Prop where
  core_normalizes : H.pCoreIn 2 ≤ normalizer (V : Set G)
  small_disjoint : ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
    IsElementaryAbelian 2 A → Disjoint A (H.pCoreIn 2) → Nat.card A ≤ 4
  residual_generation : ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
    ¬ A ≤ H.pCoreIn 2 → (pResidual 2 H).map H.subtype ≤ componentOrbit A H

omit [Finite G] in
theorem chosen_centralizer_le_of_noEscape (D : ChosenModule T L V)
    (hnone : NoEscape L V) : centralizer (V : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨v, hv, hv1⟩ := V.bot_or_exists_ne_one.resolve_left D.ne_bot
  exact (centralizer_le (Set.singleton_subset_iff.mpr hv)).trans (hnone v hv hv1)

/-- The actual centralizer premise of 12.2.7 follows from no escape. -/
theorem chosen_omega_centralizer_le_of_noEscape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hnone : NoEscape L V) :
    centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  have hi := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup V (T : Subgroup G)
    D.le_sylow T.isPGroup' (((structural G T L h).2.2 V D).1) D.ne_bot
  obtain ⟨v, hv, hv1⟩ := (V ⊓ omegaCenterIn (T : Subgroup G)).bot_or_exists_ne_one.resolve_left hi
  exact (centralizer_le (Set.singleton_subset_iff.mpr hv.2)).trans (hnone v hv.1 hv1)

/-- The original H-star subgroup is intrinsically a minimal parabolic. -/
theorem chosen_hstar_minimalParabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  have hn : normalizer (T : Set G) ≤ normalizer (L : Set G) :=
    (normalizer_le_weakClosure_normalizer V (T : Subgroup G) 0).trans
      (chosen_weakClosure_zero_local_control h D structural hTI).2.2
  apply (ChapterB.isMinimalParabolicOver_top_iff _).mpr
  refine ⟨?_, ?_⟩
  · obtain ⟨B, ⟨hBc, hBT⟩, hb⟩ := Chapter3.HStar.unique_maximal_subgroup T
      (structural G T L h).1 hH
    have hSB : ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) ≤ B := by
      intro s hs
      obtain ⟨b, hb, he⟩ := hBT hs
      exact H.subtype_injective he ▸ hb
    refine ⟨B, ⟨hBc, hSB⟩, ?_⟩
    intro C hC
    apply hb C
    refine ⟨hC.1, ?_⟩
    intro t ht
    exact ⟨⟨t, hH.1.1.2 ht⟩, hC.2 ht, rfl⟩
  · exact ((ChapterB.isMinimalParabolicOver_iff T H).mp
      (Chapter3.HStar.minimalParabolic T (structural G T L h).1 hH (Or.inl hn))).2

/-- B.6.8(4) applied to the actual H-orbit of a subgroup outside O₂(H). -/
theorem chosen_hstar_residual_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) (hAQ : ¬ A ≤ H.pCoreIn 2) :
    (pResidual 2 H).map H.subtype ≤ componentOrbit A H := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let S := T.subtype hTH
  have hp : ChapterB.IsMinimalParabolicOver S ⊤ :=
    chosen_hstar_minimalParabolic h D structural hTI hH
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

theorem hstarRankControl_of_small_disjoint
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hTI : IsTISubgroup V)
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
  exact ⟨hQT.trans (((structural G T L h).2.2 V D).1), hsmall,
    chosen_hstar_residual_generation h D structural hTI hH⟩

theorem hstarRankControl_of_quotient_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hrank : primeRank 2 (H ⧸ pCore 2 H) ≤ 2) : HStarRankControl T V H := by
  apply hstarRankControl_of_small_disjoint h D structural hTI hH
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
theorem chosen_movement_of_rank_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) (hlarge : 4 < Nat.card V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (control : HStarRankControl T V H) : ¬ V ≤ H.pCoreIn 2 := by
  intro hVQ
  let := D.elementary
  obtain ⟨g, hgT, hgQ⟩ := exists_chosen_conjugate_outside_hstar_core h D structural hTI hH
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
  exact sup_le hKM (structural G T L h).1

/-- The source application needs only the outstanding bound on H/O₂(H).
The size of V, minimal parabolicity and residual generation are discharged. -/
theorem chosen_movement_of_quotient_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hrank : primeRank 2 (H ⧸ pCore 2 H) ≤ 2) : ¬ V ≤ H.pCoreIn 2 :=
  chosen_movement_of_rank_control h D structural hnone hTI (chosen_card_gt_four h D) hH
    (hstarRankControl_of_quotient_rank h D structural hTI hH hrank)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
