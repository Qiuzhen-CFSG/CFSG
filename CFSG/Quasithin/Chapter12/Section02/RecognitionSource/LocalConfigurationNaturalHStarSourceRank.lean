module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalMovement
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.SolvableTwoRank
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic
public import Theory.SpecificGroups.Alternating.FiveResidualRank

/-!
# Rank and residual reductions for the original H-star subgroup

The local structural input at the same G,T suffices for the weak-closure
normalizer argument and intrinsic minimal parabolicity. The solvable branch
then has two-core quotient rank at most two by B.6.8 and the small odd-residual
action theorem. In the nonsolvable branch the actual A₅ identification of
O²(H)/O₂(O²(H)) suffices for that bound. This identification remains an explicit
earlier-source obligation; movement is not an input to either rank proof.

The original residual escapes N_G(L). No escape of point centralizers therefore
makes its fixed subgroup on V trivial, the noncentrality step in 12.2.19.
The nonsolvable source restrictions and the natural TI-pair/A₇ exclusion
remain to be proved. None is asserted by the conditional rank assembly.

Source: Aschbacher--Smith, 12.2.7, 12.2.17--19, printed pp.797--802.
The displayed 12.2.7(1) prints C_T(V), but its use in 12.2.18 is C_T(V_H).
The former would put the elementary V in O₂(H), contradicting movement.
The rank arguments here do not assume either centralizer equality.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

theorem chosen_hstar_residual_escape_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ (pResidual 2 H).map H.subtype ≤ normalizer (L : Set G) := by
  intro hk
  have hgen : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (Subgroup.map H.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    have ht : ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H).map H.subtype =
        (T : Subgroup G) := by
      change ((T : Subgroup G).subgroupOf H).map H.subtype = _
      exact map_subgroupOf_eq_of_le hH.1.1.2
    simpa only [Subgroup.map_sup, ht, ← MonoidHom.range_eq_map, range_subtype] using hh
  apply hH.1.2
  rw [← hgen]
  exact sup_le hk (structural L h).1

theorem chosen_hstar_residual_fixed_eq_bot_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    V ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  by_contra hn
  have hv1 : v ≠ 1 := hn
  apply chosen_hstar_residual_escape_at h structural hH
  apply le_trans _ (hnone v hv.1 hv1)
  intro k hk
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp hv.2 k hk)

/-- The normalizer control needed for minimal parabolicity uses only the
structural implication at the original ambient group and Sylow subgroup. -/
theorem chosen_normalizer_sylow_le_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let := D.elementary
  have hT := ((structural L h).2.2 V D).1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hc : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    have he := (D.fundamentalSetup h.toHypothesis1221).sylow_centralizer_module hu
    have ho : componentOrbit V (T : Subgroup G) = V :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hT)
        (le_componentOrbit V T)
    rw [D.fundamentalSetup_module, ho] at he
    simpa only [Chapter3.Section02.localJoin, D.localOrbit_eq] using he
  have hkernel : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) =
      {normalizer (L : Set G)} := by
    rw [hc]
    have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
      simpa only [D.localOrbit_eq] using hu.normalizer_maximal
    have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
        L ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G) := by
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
  have hall : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
    intro g hg
    apply hTI.conjugate_le_centralizer_of_index V (T : Subgroup G)
      T.isPGroup' D.le_sylow _ g hg
    rw [relIndex_eq_one.mpr hT]
    exact (Subgroup.one_lt_card_iff_ne_bot V).mpr D.ne_bot
  have hw : 0 < globalW V (T : Subgroup G) := by
    apply bot_lt_iff_ne_bot.mpr
    intro he
    obtain ⟨g, hg, hn⟩ := (globalW_eq_zero_iff V (T : Subgroup G)).mp he
    exact hn (hall g hg)
  exact (normalizer_le_weakClosure_normalizer V (T : Subgroup G) 0).trans
    (SourceContainment.normalizer_weakClosure_zero_le
      ⟨D.ne_bot, D.le_sylow, hT⟩ hw hkernel)

/-- Intrinsic minimal parabolicity before movement, with ambient-local input. -/
theorem chosen_hstar_minimalParabolic_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  have hp := Chapter3.HStar.minimalParabolic T (structural L h).1 hH
    (Or.inl (chosen_normalizer_sylow_le_at h D structural hTI))
  obtain ⟨hTB, hBH, _⟩ := Chapter3.HStar.unique_maximal T (structural L h).1 hH
  exact (ChapterB.intrinsic_minimalParabolic T H
    (H ⊓ normalizer (L : Set G)) hp hTB hBH).1

/-- The entire solvable rank branch, independent of movement. -/
theorem chosen_hstar_quotient_rank_of_solvable_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) : primeRank 2 (H ⧸ pCore 2 H) ≤ 2 :=
  ChapterB.solvable_minimalParabolic_twoCoreQuotient_rank_le_two
    (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1).stronglyQuasithin
    (T.subtype hH.1.1.2) (chosen_hstar_minimalParabolic_at h D structural hTI hH) hs

/-- Both rank branches assembled from the remaining exact source 12.2.7(2)
identification. The hypothesis is an actual quotient isomorphism, not a tag. -/
theorem chosen_hstar_quotient_rank_of_residual_identification_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (identify : ¬ Group.IsSolvable H →
      Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* alternatingGroup (Fin 5))) :
    primeRank 2 (H ⧸ pCore 2 H) ≤ 2 := by
  by_cases hs : Group.IsSolvable H
  · exact chosen_hstar_quotient_rank_of_solvable_at h D structural hTI hH hs
  · obtain ⟨e⟩ := identify hs
    exact Theory.SpecificGroups.Alternating.FiveExtensionAction.twoCoreQuotient_rank_le_two_of_residual_five e

/-- The preserved universal structural API feeds the same rank reduction. -/
theorem chosen_hstar_quotient_rank_of_residual_identification
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (identify : ¬ Group.IsSolvable H →
      Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* alternatingGroup (Fin 5))) :
    primeRank 2 (H ⧸ pCore 2 H) ≤ 2 :=
  chosen_hstar_quotient_rank_of_residual_identification_at h D (structural.at T) hTI hH identify

/-- The residual identification now feeds the literal 12.2.18 movement
consumer; the numerical rank callback has been discharged. -/
theorem chosen_movement_of_residual_identification
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (identify : ¬ Group.IsSolvable H →
      Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* alternatingGroup (Fin 5))) :
    ¬ V ≤ H.pCoreIn 2 :=
  chosen_movement_of_quotient_rank h D structural hnone hTI hH
    (chosen_hstar_quotient_rank_of_residual_identification h D structural hTI hH identify)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
