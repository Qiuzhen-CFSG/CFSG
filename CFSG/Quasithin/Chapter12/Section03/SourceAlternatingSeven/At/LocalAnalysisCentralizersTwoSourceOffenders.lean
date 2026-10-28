module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceOffenders
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersTwoSourceOmegaSpan

/-!
# LocalAnalysisCentralizersTwoSourceOffenders at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersTwoSourceOffenders`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 ChapterB.InternalThompsonAction Representation.BinaryOffender

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

attribute [local instance] omega_normal omega_elementary

theorem twoOmega_movement_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    ⁅P.twoOmegaModule,P.five.subgroupOf P.twoCentralizer⁆ ≠ ⊥ := by
  intro he
  apply P.five_moves_six_at structural escape
  have hh := congrArg (map P.twoCentralizer.subtype) he
  rw [map_commutator,map_subgroupOf_eq_of_le P.twoOmegaSpan_le_pointCentralizer,
    map_subgroupOf_eq_of_le P.five_le_twoCentralizer,Subgroup.map_bot] at hh
  have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
  exact hc.trans (centralizer_le (Set.singleton_subset_iff.mpr
    (le_conjugateSpanBy _ _ P.six_mem_omega)))

noncomputable def twoOmegaFiveEquiv_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hn : P.twoCentralizer ≤ normalizer (P.five : Set G)) :
    P.twoOmegaFive ≃* alternatingGroup (Fin 5) := by
  let K := P.five.subgroupOf P.twoCentralizer
  let : K.Normal := normal_subgroupOf_of_le_normalizer hn
  let e := P.twoRestrictedFiveEquiv
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    rw [map_one]
    apply mem_bot.mp
    rw [← alternatingGroup.center_eq_bot (by simp)]
    exact (centerCongr e) ⟨x,hx⟩ |>.property
  exact (reducedQuasisimpleImageEquiv P.twoOmegaModule K P.twoOmegaSpan_reduced hz
    (P.twoOmega_movement_at structural escape)).symm.trans e

theorem twoOmegaFive_le_offenders_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    P.twoOmegaFive ≤ offenderSubgroup P.twoOmegaAction := by
  let H := P.twoCentralizer
  have hTH : (T : Subgroup G) ≤ H := fun t ht =>
    mem_centralizer_singleton_iff.mpr (P.two_central t ht)
  let R := T.subtype hTH
  let K := P.five.subgroupOf H
  let J := Stellmacher.elementaryAbelianMaxJ (R : Subgroup H)
  have hj : J.map H.subtype = Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← Stellmacher.elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le hTH
  have hk : K = ⁅K,J⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le P.five_le_twoCentralizer,hj]
    exact (PointCentralizers.source_1237_at P structural escape).2.2.2.2.1
  let : (offenderSubgroup P.twoOmegaAction).Normal := offenderSubgroup_normal _
  change K.map P.twoOmegaMap ≤ _
  rw [hk,map_commutator]
  exact (commutator_mono le_rfl (thompson_image_le R P.twoOmegaModule)).trans
    (commutator_le_right _ _)

theorem twoOmegaFive_component_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    IsComponent (offenderSubgroup P.twoOmegaAction)
      (P.twoOmegaFive.subgroupOf (offenderSubgroup P.twoOmegaAction)) := by
  have hn := P.two_source_normalizes_at structural modules escape natural
  let K := P.five.subgroupOf P.twoCentralizer
  let : K.Normal := normal_subgroupOf_of_le_normalizer hn
  let : P.twoOmegaFive.Normal := Normal.map inferInstance P.twoOmegaMap
    (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let e := (subgroupOfEquivOfLe (P.twoOmegaFive_le_offenders_at structural escape)).trans
    (P.twoOmegaFiveEquiv_at structural escape hn)
  exact ⟨(inferInstance : (P.twoOmegaFive.subgroupOf
    (offenderSubgroup P.twoOmegaAction)).Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv e.symm⟩

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

