module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceOmegaSpan
public import Theory.GroupTheory.ReducedNormal.QuasisimpleImage
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
/-!
# The original A₅ component in the omega-span offender action

B.2.14 supplies the reduced module inside the actual point centralizer.
The original A₅ residual acts nontrivially, so its faithful image is A₅.
The Thompson identity places that image in the offender subgroup, where
relative normality makes it an ordinary component. The involution centralizer
provides the genuine SQTK cover required by B.5.6.

Source: Aschbacher–Smith 12.3.8, p.810, with B.2.14 and B.5.3–6.
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

abbrev twoCentralizer := centralizer ({(P.two : G)} : Set G)
abbrev twoOmegaModule := P.twoOmegaSpan.subgroupOf P.twoCentralizer
local instance omega_normal : P.twoOmegaModule.Normal := P.twoOmegaSpan_reduced.normal
local instance omega_elementary : IsElementaryAbelian 2 P.twoOmegaModule := P.twoOmegaSpan_reduced.elementary
abbrev twoOmegaQuotient := ActionQuotient P.twoOmegaModule
abbrev twoOmegaMap : P.twoCentralizer →* P.twoOmegaQuotient := actionMk P.twoOmegaModule
abbrev twoOmegaAction : Representation (ZMod 2) P.twoOmegaQuotient (Additive P.twoOmegaModule) := action P.twoOmegaModule
abbrev twoOmegaFive : Subgroup P.twoOmegaQuotient := (P.five.subgroupOf P.twoCentralizer).map P.twoOmegaMap

theorem five_le_twoCentralizer : P.five ≤ P.twoCentralizer :=
  (pointResidual_le L (P.two : G)).trans inf_le_right

def twoRestrictedFiveEquiv :
    (P.five.subgroupOf P.twoCentralizer ⧸ pCore 2 (P.five.subgroupOf P.twoCentralizer)) ≃*
      alternatingGroup (Fin 5) :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe P.five_le_twoCentralizer)
    (pCore_map_iso 2 _)).trans P.fiveCoreEquiv

theorem twoOmega_movement
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    ⁅P.twoOmegaModule,P.five.subgroupOf P.twoCentralizer⁆ ≠ ⊥ := by
  intro he
  apply P.five_moves_six structural escape
  have hh := congrArg (map P.twoCentralizer.subtype) he
  rw [map_commutator,map_subgroupOf_eq_of_le P.twoOmegaSpan_le_pointCentralizer,
    map_subgroupOf_eq_of_le P.five_le_twoCentralizer,Subgroup.map_bot] at hh
  have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
  exact hc.trans (centralizer_le (Set.singleton_subset_iff.mpr
    (le_conjugateSpanBy _ _ P.six_mem_omega)))

noncomputable def twoOmegaFiveEquiv
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
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
    (P.twoOmega_movement structural escape)).symm.trans e


theorem twoOmegaFive_le_offenders
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
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
    exact (PointCentralizers.source_1237 P structural escape).2.2.2.2.1
  let : (offenderSubgroup P.twoOmegaAction).Normal := offenderSubgroup_normal _
  change K.map P.twoOmegaMap ≤ _
  rw [hk,map_commutator]
  exact (commutator_mono le_rfl (thompson_image_le R P.twoOmegaModule)).trans
    (commutator_le_right _ _)

theorem twoOmega_classification :
    ChapterB.SourceInduction.AdequateAlternative
      (P.twoOmegaAction.comp (offenderSubgroup P.twoOmegaAction).subtype) := by
  have ho : orderOf (P.two : G) = 2 :=
    orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp P.two_mem_omega).2.2 P.two_ne_one
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      P.twoOmegaQuotient := {
    Cover := P.twoCentralizer
    kernel := centralizer (P.twoOmegaModule : Set P.twoCentralizer)
    sqtk := Chapter3.sqtk_of_mem_H S.hypothesis.simpleQTKE
      (Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer ho))
    equiv := MulEquiv.refl _ }
  exact ChapterB.SourceInduction.offenderSubgroup_adequateAlternative P.twoOmegaAction
    (action_faithful _) P.twoOmegaSpan_reduced.quotient_pCore_eq_bot c

/-- The original A₅ is an ordinary component of the actual offender actor. -/
theorem twoOmegaFive_component
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    IsComponent (offenderSubgroup P.twoOmegaAction)
      (P.twoOmegaFive.subgroupOf (offenderSubgroup P.twoOmegaAction)) := by
  have hn := P.two_source_normalizes structural modules escape natural
  let K := P.five.subgroupOf P.twoCentralizer
  let : K.Normal := normal_subgroupOf_of_le_normalizer hn
  let : P.twoOmegaFive.Normal := Normal.map inferInstance P.twoOmegaMap
    (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let e := (subgroupOfEquivOfLe (P.twoOmegaFive_le_offenders structural escape)).trans
    (P.twoOmegaFiveEquiv structural escape hn)
  exact ⟨(inferInstance : (P.twoOmegaFive.subgroupOf
    (offenderSubgroup P.twoOmegaAction)).Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv e.symm⟩

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
