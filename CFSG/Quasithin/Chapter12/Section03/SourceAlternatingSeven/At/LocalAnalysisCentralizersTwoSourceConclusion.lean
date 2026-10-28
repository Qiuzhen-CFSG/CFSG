module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceConclusion
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersTwoSourceOffenders

/-!
# LocalAnalysisCentralizersTwoSourceConclusion at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersTwoSourceConclusion`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

attribute [local instance] conclusionOmegaNormal conclusionOmegaElementary

theorem twoOmegaFive_moved_irrPlus_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    IsIrrPlus P.twoOmegaAction P.twoOmegaFive
      (subspaceCommutator P.twoOmegaAction ⊤ P.twoOmegaFive) := by
  have hle := P.twoOmegaFive_le_offenders_at structural escape
  let e := (subgroupOfEquivOfLe hle).trans (P.twoOmegaFiveEquiv_at structural escape
    (P.two_source_normalizes_at structural modules escape natural))
  have hc : Nat.card (P.twoOmegaFive.subgroupOf (offenderSubgroup P.twoOmegaAction)) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hi := P.twoOmega_classification.card60_component_moved
    (P.twoOmegaFive_component_at structural modules escape natural) hc
  rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hle] at hi
  exact (IsIrrPlus.subgroupOf_iff _ _ _ hle _).mp hi

theorem twoOmegaSpan_commutator_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    ⁅P.twoOmegaSpan,P.five⁆ = ⁅V,P.five⁆ := by
  let H := P.twoCentralizer
  let K := P.five.subgroupOf H
  let M := ⁅V,P.five⁆.subgroupOf H
  have hMH : ⁅V,P.five⁆ ≤ H :=
    (P.five_moved_le_omegaSpan_at structural escape).trans P.twoOmegaSpan_le_pointCentralizer
  let : Group.IsPerfect P.five := Chapter1.mem_L_isPerfect (P.five_local_family_at structural)
  let e := P.twoOmegaFiveEquiv_at structural escape
    (P.two_source_normalizes_at structural modules escape natural)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect P.twoOmegaFive :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hn : K ≤ normalizer (M : Set H) := by
    intro k hk
    apply mem_normalizer_iff.mpr
    intro m
    exact mem_normalizer_iff.mp (normalizer_commutator_ge_right V P.five hk) m
  have hm : ⁅M,K⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (map H.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hMH,
      map_subgroupOf_eq_of_le P.five_le_twoCentralizer,Subgroup.map_bot] at hh
    have hz := commutator_eq_bot_of_iterated_eq_bot V P.five hh
    rw [←P.five_omega_commutator_at structural escape] at hz
    apply P.five_moves_six_at structural escape
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
      (centralizer_le (Set.singleton_subset_iff.mpr P.six_mem_omega))
  have hle := NormalElementaryQuotient.commutator_le_of_noncentral_invariant
    P.twoOmegaModule M K (fun _ hx => P.five_moved_le_omegaSpan_at structural escape hx)
    hn P.twoOmegaMap (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (P.twoOmegaFive_moved_irrPlus_at structural modules escape natural) hm
  have hh := Subgroup.map_mono (f := H.subtype) hle
  rw [map_commutator,map_subgroupOf_eq_of_le P.twoOmegaSpan_le_pointCentralizer,
    map_subgroupOf_eq_of_le P.five_le_twoCentralizer,map_subgroupOf_eq_of_le hMH] at hh
  exact P.two_omegaSpan_commutator_eq_of_le_at structural escape hh

end SylowNormalizer.Points

namespace PointCentralizers

theorem source_twoInput_at (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    TwoInput P := by
  have hn := P.two_source_normalizes_at structural modules escape natural
  exact ⟨hn,P.two_section_fixes_moved_of_normalizes_at structural
    ((ChapterA.Section04.twoSectionCentralizer_le _ _).trans
      (P.two_moved_normalized_of_omegaSpan_commutator hn
        (P.twoOmegaSpan_commutator_at structural modules escape natural)))⟩

theorem source_pointCentralizers_at (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (v : V) (hv : v ≠ 1)
    (hw : BinarySevenCode.weight (E.coordinates v).toAdd.val = 2 ∨
      BinarySevenCode.weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) :=
  pointCentralizers_at P (source_sixInput_at P structural)
    (source_twoInput_at P structural modules escape natural) structural v hv hw

def source_localAnalysis_at (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    S.LocalAnalysis :=
  localAnalysis_of_twoInput_at P structural (source_twoInput_at P structural modules escape natural)

end PointCentralizers

namespace Setup.NaturalCoordinates

variable (E : S.NaturalCoordinates)

def sourcePoints_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) : SylowNormalizer.Points E := by
  let ht := E.central_representative_weight_at structural (n := 2) (Or.inl rfl)
  let hs := E.central_representative_weight_at structural (n := 6) (Or.inr (Or.inr rfl))
  exact ⟨ht.choose,hs.choose,ht.choose_spec.1,hs.choose_spec.1,
    ht.choose_spec.2,hs.choose_spec.2⟩

theorem source_point_centralizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (v : V) (hv : v ≠ 1)
    (hw : BinarySevenCode.weight (E.coordinates v).toAdd.val = 2 ∨
      BinarySevenCode.weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) :=
  PointCentralizers.source_pointCentralizers_at (E.sourcePoints_at structural)
    structural modules escape natural v hv hw

def source_localAnalysis_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    S.LocalAnalysis :=
  PointCentralizers.source_localAnalysis_at (E.sourcePoints_at structural)
    structural modules escape natural

end Setup.NaturalCoordinates

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

