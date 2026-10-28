module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal.CorankTwo
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.TI
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment

/-!
# Containment and the terminal contradiction from corank-two weak closure

For the original U=[R₂(N_G(L)),L], the small-section argument makes
W₂(T,U) centralize U. Thus both weak-closure parameters are greater than
two. E.3.35 now puts every genuinely E-generated-at-two overgroup of T
inside N_G(L). This bypasses the final A₅ TI-pair recognition on p.876.

The source normalizer uniqueness over N_G(C_T(U)) and construction of an
escaping E-generated overgroup remain explicit. The numerical n(H)=1
clause uses positive attainment, not an infimum over an empty family.

Source: Aschbacher--Smith 13.1.14 and the end of 13.1.7, pp.875--876;
E.3.35(1), pp.238--239.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual moved module has both source parameters greater than two.
Only TI remains as an earlier source premise. -/
theorem normalizerMoved_parameters_gt_two
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hTI : IsTISubgroup (normalizerMoved L)) :
    2 < ChapterE.globalW (normalizerMoved L) (T : Subgroup G) ∧
      2 < ChapterE.globalR (normalizerMoved L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨hU,hne,_,hN⟩ := faithful_maximal_normalizer_moved h.simpleQTKE hL hTL
  let := hU
  obtain ⟨hmoved,hsize⟩ := normalizerMoved_commutator_and_card hL.1.1 hne
  have hLU : L ≤ normalizer (normalizerMoved L : Set G) := by rw [hN];exact L.le_normalizer
  have hTU : (T : Subgroup G) ≤ normalizer (normalizerMoved L : Set G) := by rw [hN];exact hTL
  have hr : (3 : ℕ∞) ≤ ChapterE.globalR (normalizerMoved L) := by
    apply le_iInf
    intro D
    apply le_iInf
    rintro ⟨hD,hescape⟩
    have hbot : D = ⊥ := by
      by_contra hbot
      obtain ⟨d,hd⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
      have hd1 : (d : G) ≠ 1 := fun he => hd (Subtype.ext he)
      apply hescape
      exact (centralizer_le (show ({(d : G)} : Set G) ⊆ D from
        Set.singleton_subset_iff.mpr d.property)).trans
        (hTI.centralizer_le_normalizer (hD d.property) hd1)
    subst D
    change (3 : ℕ∞) ≤ (Nat.log 2 ((⊥ : Subgroup G).relIndex (normalizerMoved L)) : ℕ∞)
    rw [relIndex_bot_left]
    exact_mod_cast (Nat.le_log_of_pow_le (by decide : 1 < 2) hsize)
  exact ⟨globalW_gt_two h.simpleQTKE T hL.1.1 hn hTI hLU
    (solvableRadical_centralizes_normalizerMoved h hmany hL.1 hn)
    hmoved hsize hTU hN.le, lt_of_lt_of_le (by decide : (2 : ℕ∞) < 3) hr⟩

/-- The strengthened weak-closure conclusion on the literal source module. -/
theorem normalizerMoved_weakClosure_two_centralizes
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hTI : IsTISubgroup (normalizerMoved L)) :
    ChapterE.indexedWeakClosure (normalizerMoved L) (T : Subgroup G) 2 ≤
      centralizer (normalizerMoved L : Set G) :=
  (ChapterE.weakClosure_le_centralizer_of_lt_globalW
    (normalizerMoved_parameters_gt_two h hmany hL hn hTI).1).trans inf_le_right

private theorem moved_E322
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ∃ he : IsElementaryAbelian 2 (normalizerMoved L),
      @ChapterE.HypothesisE322 G _ (normalizerMoved L) T he := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨he,hne,hcore,hN⟩ := faithful_maximal_normalizer_moved h.simpleQTKE hL hTL
  refine ⟨he,hne,?_,?_⟩
  · apply hcore.trans
    have hi := pCoreIn_le_sylow (normalizer (L : Set G)) (T.subtype hTL)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTL] at hi
  · rwa [hN]

/-- The normalizer clause of original 13.1.14(1), from the source uniqueness
at C_T(U), with the weak-closure hypotheses discharged. -/
theorem normalizer_weakClosure_zero_le
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hTI : IsTISubgroup (normalizerMoved L))
    (hunique : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (normalizerMoved L : Set G) : Subgroup G) : Set G)) =
        {normalizer (L : Set G)}) :
    normalizer (ChapterE.indexedWeakClosure (normalizerMoved L) (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G) := by
  obtain ⟨he,hE⟩ := moved_E322 h hL hn
  let := he
  exact ChapterE.SourceContainment.normalizer_weakClosure_zero_le hE
    (lt_trans (by decide : (0 : ℕ∞) < 2)
      (normalizerMoved_parameters_gt_two h hmany hL hn hTI).1) hunique

/-- Every actual E-generated-at-two overgroup of T is contained in M.
This is the strengthened containment used in the terminal contradiction. -/
theorem le_normalizer_of_isEGenerated_two
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hTI : IsTISubgroup (normalizerMoved L))
    (hunique : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (normalizerMoved L : Set G) : Subgroup G) : Set G)) =
        {normalizer (L : Set G)})
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hgen : ChapterE.IsEGenerated 2 H) : H ≤ normalizer (L : Set G) := by
  obtain ⟨he,hE⟩ := moved_E322 h hL hn
  let := he
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hN := (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).2.2.2
  obtain ⟨hw,hr⟩ := normalizerMoved_parameters_gt_two h hmany hL hn hTI
  apply ChapterE.SourceContainment.le_of_isEGenerated hE (T.subtype hTH)
    (hgen (T.subtype hTH)) hunique ?_ ?_ hw hr
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hN.le)
  · rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
    exact inf_le_left

/-- Original 13.1.14(3), using the attained positive value n(H)=1. -/
theorem le_normalizer_of_generationParameter_eq_one
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hTI : IsTISubgroup (normalizerMoved L))
    (hunique : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (normalizerMoved L : Set G) : Subgroup G) : Set G)) =
        {normalizer (L : Set G)})
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hgen : ChapterE.generationParameter H = 1) : H ≤ normalizer (L : Set G) := by
  have hg : ChapterE.IsEGenerated 1 H := by
    have hp : 0 < ChapterE.generationParameter H := by omega
    simpa only [hgen] using ChapterE.isEGenerated_generationParameter_of_pos hp
  exact le_normalizer_of_isEGenerated_two h hmany hL hn hTI hunique hTH
    (hg.mono (by decide))

/-- A shorter terminal contradiction: source escape and actual E-generation
at two contradict the proved corank-two containment. -/
theorem false_of_escaping_two_generated
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hTI : IsTISubgroup (normalizerMoved L))
    (hunique : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (normalizerMoved L : Set G) : Subgroup G) : Set G)) =
        {normalizer (L : Set G)})
    (hescape : ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧ ChapterE.IsEGenerated 2 H) : False := by
  obtain ⟨H,hTH,hout,hgen⟩ := hescape
  exact hout (le_normalizer_of_isEGenerated_two h hmany hL hn hTI hunique hTH hgen)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceNonquasisimple.Terminal ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- Application to the actual 13.3.1 maximal nonquasisimple counterexample.
The source normalizer and escaping-generation constructions remain explicit. -/
theorem Hypothesis1331.false_of_nonquasisimple_terminal_inputs
    (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀))
    (hTI : ∀ K : Subgroup G, L₀ ≤ K → FaithfulMaximalLocal T K →
      ¬ IsQuasisimple (XiQuotient K) → IsTISubgroup (normalizerMoved K))
    (hcontrol : ∀ K : Subgroup G, L₀ ≤ K → FaithfulMaximalLocal T K →
      ¬ IsQuasisimple (XiQuotient K) → maximalTwoLocalOvergroups (normalizer
        (((T : Subgroup G) ⊓ centralizer (normalizerMoved K : Set G) : Subgroup G) : Set G)) =
          {normalizer (K : Set G)})
    (hescape : ∀ K : Subgroup G, L₀ ≤ K → FaithfulMaximalLocal T K →
      ¬ IsQuasisimple (XiQuotient K) → ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧
        ¬ H ≤ normalizer (K : Set G) ∧ ChapterE.IsEGenerated 2 H) : False := by
  obtain ⟨K,hK,hLK,hf,hkn,_⟩ := h.maximal_counterexample_of_many hmany hn
  exact false_of_escaping_two_generated h.hypothesis1311 hmany hf hkn.2
    (hTI K hLK hf hkn.2) (hcontrol K hLK hf hkn.2) (hescape K hLK hf hkn.2)

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
