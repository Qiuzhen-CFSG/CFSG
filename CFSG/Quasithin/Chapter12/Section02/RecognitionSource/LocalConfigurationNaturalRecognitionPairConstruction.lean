module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalRecognitionInputs
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.FullAxis
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.SolvableTwoRank
public import Theory.GroupTheory.CentralPChiefCore
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# Odd conjugators and nontrivial TI pairs in the solvable H-star branch

Movement of V outside O₂(H) forces some odd-order element of O²(H) to move V:
otherwise its odd-order generators, together with T, would normalize V.
The intrinsic solvable minimal-parabolic theorem bounds the two-rank of
H/O₂(H) by two. Since |V| > 4, the intersection V ∩ O₂(H) is nontrivial.
The core normalizes every H-conjugate of V, so the constructed pair has
nontrivial mutual normalizers, whose product lies in its relative two-core.

A second construction chooses a noncommuting conjugate pair. Otherwise all
conjugates would generate an elementary abelian normal subgroup containing V,
contradicting movement. Its mutual normalizer is therefore nontrivial and proper.

These are actual pairs under the original source hypotheses. The hyperplane
property and a V-invariant cyclic odd subgroup remain stronger steps.
Source: Aschbacher–Smith, B.6.8(2), pp.113–114, I.6.2(2a), pp.424–425,
and the construction immediately before 12.2.20, printed p.802.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

theorem chosen_exists_odd_conjugator_of_movement (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hm : ¬ V ≤ H.pCoreIn 2) :
    ∃ g ∈ (pResidual 2 H).map H.subtype, Odd (orderOf g) ∧
      V.map (MulAut.conj g).toMonoidHom ≠ V := by
  let := D.elementary
  let K := pResidual 2 H
  let f : K →* G := H.subtype.comp K.subtype
  have hgen : K.map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (Subgroup.map H.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hTH))
    simpa only [Subgroup.map_sup, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hmove : ¬ K.map H.subtype ≤ normalizer (V : Set G) := by
    intro hn
    have hHN : H ≤ normalizer (V : Set G) := by
      rw [← hgen]
      exact sup_le hn hT
    exact hm (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
      (D.le_sylow.trans hTH) hHN)
  have hoddgen := closure_coprime_order_eq_top_of_pResidual_eq_top 2
    ((pResidual_eq_top_iff 2 K).mpr (isPPerfect_pResidual 2))
  have hex : ∃ k : K, Nat.Coprime 2 (orderOf k) ∧ f k ∉ normalizer (V : Set G) := by
    by_contra! hn
    have hle : closure {k : K | Nat.Coprime 2 (orderOf k)} ≤
        (normalizer (V : Set G)).comap f := by
      rw [closure_le]
      exact hn
    rw [hoddgen] at hle
    apply hmove
    rintro x ⟨k, hk, rfl⟩
    exact hle (mem_top (⟨k, hk⟩ : K))
  obtain ⟨k, hk, hn⟩ := hex
  refine ⟨f k, mem_map_of_mem H.subtype k.property, ?_, ?_⟩
  · rw [orderOf_injective f (H.subtype_injective.comp K.subtype_injective)]
    exact Nat.coprime_two_left.mp hk
  · exact fun he => hn (mem_normalizer_iff_map_conj_eq.mpr he)

theorem chosen_solvable_core_intersection_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2) :
    V ⊓ H.pCoreIn 2 ≠ ⊥ := by
  let := D.elementary
  have hrank := ChapterB.solvable_minimalParabolic_twoCoreQuotient_rank_le_two
    (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1).stronglyQuasithin
    (T.subtype hH.1.1.2) (chosen_hstar_minimalParabolic_of_movement D hH hm) hs
  intro he
  have hd : Disjoint V (H.pCoreIn 2) := disjoint_iff.mpr he
  let i : V →* H := inclusion (D.le_sylow.trans hH.1.1.2)
  let f : V →* (H ⧸ pCore 2 H) := (QuotientGroup.mk' (pCore 2 H)).comp i
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply bot_unique
    intro a ha
    change a = 1
    apply Subtype.ext
    apply hd.le_bot
    exact ⟨a.property,
      mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff (i a)).mp ha)⟩
  have hr := (Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans hrank
  have hc : Nat.card V ≤ 4 := by
    rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) V]
    exact Nat.pow_le_pow_right (by decide) hr
  exact (not_lt_of_ge hc) (chosen_card_gt_four h D)

omit [Finite G] in
theorem chosen_core_normalizes_conjugate
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H) {g : G} (hg : g ∈ H) :
    H.pCoreIn 2 ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hQN : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have he : (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom = H.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hQN hg)
  rw [← he]
  exact (map_mono (hQT.trans hT)).trans (V.le_normalizer_map (MulAut.conj g).toMonoidHom)

theorem chosen_exists_odd_ti_pair_of_solvable_movement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2) :
    ∃ g ∈ (pResidual 2 H).map H.subtype, Odd (orderOf g) ∧
      Disjoint V (V.map (MulAut.conj g).toMonoidHom) ∧
      V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) ≠ ⊥ ∧
      (V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ⊔
          (V.map (MulAut.conj g).toMonoidHom ⊓ normalizer (V : Set G)) ≤
        (V ⊔ V.map (MulAut.conj g).toMonoidHom).pCoreIn 2 := by
  let := D.elementary
  obtain ⟨g, hg, ho, hne⟩ := chosen_exists_odd_conjugator_of_movement D hT hH.1.1.2 hm
  have hd := ((hTI.eq_or_disjoint_conjugate g).resolve_left hne).symm
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  refine ⟨g, hg, ho, hd, ?_,
    ti_pair_mutual_normalizers_le_twoCore V _ hd hTI (hTI.map_equiv _)⟩
  have hQ := chosen_core_normalizes_conjugate hT hH.1.1.2 (map_subtype_le _ hg)
  intro he
  exact chosen_solvable_core_intersection_ne_bot h D hH hs hm
    (bot_unique ((inf_le_inf_left V hQ).trans_eq he))

omit [Finite G] in
private theorem exists_noncommuting_conjugate (W : Subgroup G)
    [IsElementaryAbelian 2 W] (hm : ¬ W ≤ pCore 2 G) :
    ∃ g : G, ¬ W.map (MulAut.conj g).toMonoidHom ≤ centralizer (W : Set G) := by
  by_contra! hall
  let N := normalClosure (W : Set G)
  have hnW : N ≤ centralizer (W : Set G) := by
    change closure (Group.conjugatesOfSet (W : Set G)) ≤ _
    rw [closure_le]
    intro x hx
    obtain ⟨w, hw, hg⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hg
    exact hall g (mem_map_of_mem (MulAut.conj g).toMonoidHom hw)
  have hNN : N ≤ centralizer (N : Set G) :=
    normalClosure_le_normal (le_centralizer_iff.mp hnW)
  let : IsMulCommutative N := le_centralizer_iff_isMulCommutative.mp hNN
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.normalClosure_of_isMulCommutative W
  exact hm (le_normalClosure.trans (le_sSup
    ⟨inferInstance, IsElementaryAbelian.isPGroup 2 N⟩))

/-- Movement supplies a noncommuting conjugate, so the elementary TI theorem
makes its nontrivial mutual normalizer proper. This is the entry to I.6.2(2). -/
theorem chosen_exists_proper_ti_pair_of_solvable_movement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2) :
    ∃ g ∈ H, Disjoint V (V.map (MulAut.conj g).toMonoidHom) ∧
      V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) ≠ ⊥ ∧
      V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) ≠ V := by
  let := D.elementary
  have hVH : V ≤ H := D.le_sylow.trans hH.1.1.2
  let W := V.subgroupOf H
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  have hW : ¬ W ≤ pCore 2 H := by
    intro hW
    apply hm
    intro v hv
    exact mem_map_of_mem H.subtype (hW (show (⟨v, hVH hv⟩ : H) ∈ W from hv))
  obtain ⟨g, hg⟩ := exists_noncommuting_conjugate W hW
  let A := V.map (MulAut.conj (g : G)).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hn : ¬ A ≤ centralizer (V : Set G) := by
    intro hn
    apply hg
    rintro x ⟨v, hv, rfl⟩ w hw
    apply Subtype.ext
    exact hn (mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom hv) w hw
  have hneq : A ≠ V := by
    intro he
    apply hn
    rw [he]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hd := ((hTI.eq_or_disjoint_conjugate g).resolve_left hneq).symm
  refine ⟨g, g.property, hd, ?_, ?_⟩
  · have hQ := chosen_core_normalizes_conjugate hT hH.1.1.2 g.property
    intro he
    exact chosen_solvable_core_intersection_ne_bot h D hH hs hm
      (bot_unique ((inf_le_inf_left V hQ).trans_eq he))
  · intro he
    exact hn (le_centralizer_iff.mp (ti_pair_commute_of_full_normalizer V A hd hTI
      (hTI.map_equiv _) (card_map_of_injective (MulAut.conj (g : G)).injective).symm he))


end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
