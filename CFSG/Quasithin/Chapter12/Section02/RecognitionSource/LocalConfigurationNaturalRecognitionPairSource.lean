module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalRecognitionPairConstruction
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalRecognitionPairNormalizer
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.QuotientHyperplane
public import Theory.GroupTheory.PCoreFrattiniQuotient

/-!
# The solvable TI-pair full axis

For a moving solvable H-star member, B.6.8 gives a normal odd-prime core
R in H/O₂(H) with two-group quotient. It is self-centralizing, so the
nontrivial image of V acts nontrivially on R. Coprime action yields an inverted
cyclic line in R. The quotient kernel normalizes V, and the quotient-hyperplane
lemma lifts an odd conjugator giving a literal pair with hyperplane N_V(V^g).

The opposite mutual normalizer induces the full radical on V. NoEscape puts
it in N_G(L), and the normalizer-image argument transfers this radical to the
original LT action, discharging ChosenFullAxis under exactly the original
hypotheses. The two consumer applications retain the original quotient marking
as the independent input owned by the final natural-recognition assembly.

This route needs no V-invariant odd subgroup upstairs and no full I.6.2
odd-dihedral classification. Its two-core is always the relative subgroup
inside the generated pair, as in PairElementary.FullAxis.
Source: Aschbacher–Smith, B.6.8(2), pp.113–114; I.6.2(2a), pp.424–425;
12.2.10 and the construction before 12.2.20, printed pp.798,802.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

theorem chosen_exists_hyperplane_pair_of_solvable_movement
    (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2) :
    ∃ g ∈ (pResidual 2 H).map H.subtype, Odd (orderOf g) ∧
      (letI := D.elementary
       IsCoatom (pairAxisSpace V (V.map (MulAut.conj g).toMonoidHom))) := by
  let := D.elementary
  have hVH : V ≤ H := D.le_sylow.trans hH.1.1.2
  let W := V.subgroupOf H
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  have hWTI : IsTISubgroup W := by
    apply (isTISubgroup_iff W).mpr
    intro g hg x hx hgx
    apply Subtype.ext
    apply (isTISubgroup_iff V).mp hTI g ?_ x hx hgx
    intro hn
    exact hg (V.le_normalizer_comap H.subtype hn)
  let q := QuotientGroup.mk' (pCore 2 H)
  let E := W.map q
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hWQ : ¬ W ≤ pCore 2 H := by
    intro hw
    apply hm
    intro v hv
    exact mem_map_of_mem H.subtype (hw (show (⟨v, hVH hv⟩ : H) ∈ W from hv))
  have hE : E ≠ ⊥ := by
    intro he
    apply hWQ
    have hle := (map_eq_bot_iff W (f := q)).mp he
    simpa only [q, QuotientGroup.ker_mk'] using hle
  have hk : q.ker ≤ normalizer (W : Set H) := by
    rw [QuotientGroup.ker_mk']
    have hQT := (pCore_isPGroup (p := 2) (G := H)).le_sylow_of_normal (T.subtype hH.1.1.2)
    intro x hx
    exact V.le_normalizer_comap H.subtype (hT (hQT hx))
  obtain ⟨p, hp, ho, _, hquot, _⟩ := chosen_hstar_solvable_structure_of_movement D hH hs hm
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    norm_num at ho
  let R := pCore p (H ⧸ pCore 2 H)
  have hdis : Disjoint E R := IsPGroup.disjoint_of_ne 2 p hp2.symm E R
    (IsElementaryAbelian.isPGroup 2 E) pCore_isPGroup
  have hmove : ⁅R, E⁆ ≠ ⊥ := by
    intro he
    have hER : E ≤ R := (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp he)).trans
      (centralizer_pCore_le_of_quotient_isPGroup p 2
        (pCore_quotient_pCore_eq_bot 2) hquot)
    exact hE (bot_unique ((le_inf le_rfl hER).trans hdis.le_bot))
  obtain ⟨g, hgodd, hgi⟩ := exists_odd_pair_index_two_of_quotient_action W hWTI q
    (QuotientGroup.mk'_surjective _) hk hp2 R pCore_isPGroup
    (le_normalizer_of_normal) hmove
  let A := V.map (MulAut.conj (g : G)).toMonoidHom
  have hAH : A ≤ H := by
    rintro x ⟨v, hv, rfl⟩
    exact H.mul_mem (H.mul_mem g.property (hVH hv)) (H.inv_mem g.property)
  have heA : W.map (MulAut.conj g).toMonoidHom = A.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom hv
    · rintro ⟨v, hv, hve⟩
      exact ⟨⟨v, hVH hv⟩, hv, Subtype.ext hve⟩
  rw [heA, ← subgroupOf_normalizer_eq hAH, relIndex_subgroupOf hVH] at hgi
  refine ⟨g, mem_map_of_mem H.subtype ?_, ?_, pairAxisSpace_isCoatom_of_index_two V A hgi⟩
  · exact mem_pResidual_of_orderOf_coprime (Nat.coprime_two_left.mpr hgodd)
  · simpa only [Subgroup.orderOf_coe] using hgodd

/-- The solvable H-star branch supplies the full axis in the original LT image. -/
theorem chosenFullAxis_of_solvable_movement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2) :
    ChosenFullAxis D (((structural L h).2.2 V D).1) := by
  obtain ⟨g, _, _, hg⟩ := chosen_exists_hyperplane_pair_of_solvable_movement D
    (((structural L h).2.2 V D).1) hTI hH hs hm
  exact chosenFullAxis_of_pair_hyperplane h D structural hnone hTI g hg

/-- The full-axis input is applied to the literal chosen join action. -/
theorem chosenJoinLinearAction_range_eq_top_of_solvable_movement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2) :
    letI := D.elementary
    (chosenJoinLinearAction D (((structural L h).2.2 V D).1)).range = ⊤ :=
  chosenJoinLinearAction_range_eq_top_of_full_axis_at h D structural
    (chosenFullAxis_of_solvable_movement h D structural hnone hTI hH hs hm)

/-- The original natural-action consumer has its solvable full-axis premise
fully discharged. The independent quotient marking belongs to the source
assembly owners qt-d-12213-hstar-natural and qt-d-12213-cyclic-block. -/
theorem natural_action_of_solvable_movement_and_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2)
    (markingStep : (letI := D.elementary
      (chosenJoinLinearAction D (((structural L h).2.2 V D).1)).range = ⊤) →
      ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
        (Representation.specialLinearNatural (k := ZMod 2) d))) :
    ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) d) :=
  natural_action_of_solvable_axis_and_marking h D structural hnone hTI hH hs hm
    (fun hnone hTI hH hs hm =>
      chosenFullAxis_of_solvable_movement h D structural hnone hTI hH hs hm) markingStep

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
