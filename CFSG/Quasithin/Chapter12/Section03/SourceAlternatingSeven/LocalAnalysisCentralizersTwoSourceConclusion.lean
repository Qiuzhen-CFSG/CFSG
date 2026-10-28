module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceOffenders
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.AlternatingFiveComponent
public import Theory.Representation.NormalElementaryQuotient.NoncentralContainment

/-!
# Source 12.3.6–8: both ambient point-centralizer bounds

The actual A₅ image on U=⟨Ω₁Z(T)^{C_G(e(2))}⟩ is a component of the offender
actor. The complete B.5 comparison makes its moved space Irr⁺. The original
noncentral seed [V,K] therefore contains [U,K], giving equality. Relative
normality now preserves [V,K], and the faithful natural A₅ commutant makes
the original section centralizer fix a weight-six point. The KTY cover
finishes the weight-two bound. Component orbits give both bounds at every
point and feed the original LocalAnalysis constructor.

All local rigidity and module premises are discharged. The uniform natural
coordinate input is the permitted earlier-source premise, discharged by
qt-d-1231-local-analysis; the weight-six bound and 12.3.7 remain re-exported.
Source: Aschbacher–Smith 12.3.6–8, printed pp.809–810.
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
local instance conclusionOmegaNormal : P.twoOmegaModule.Normal := P.twoOmegaSpan_reduced.normal
local instance conclusionOmegaElementary : IsElementaryAbelian 2 P.twoOmegaModule := P.twoOmegaSpan_reduced.elementary

/-- B.5.1 and B.5.6 apply to the actual A₅ component on the source omega span. -/
theorem twoOmegaFive_moved_irrPlus
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    IsIrrPlus P.twoOmegaAction P.twoOmegaFive
      (subspaceCommutator P.twoOmegaAction ⊤ P.twoOmegaFive) := by
  have hle := P.twoOmegaFive_le_offenders structural escape
  let e := (subgroupOfEquivOfLe hle).trans (P.twoOmegaFiveEquiv structural escape
    (P.two_source_normalizes structural modules escape natural))
  have hc : Nat.card (P.twoOmegaFive.subgroupOf (offenderSubgroup P.twoOmegaAction)) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hi := P.twoOmega_classification.card60_component_moved
    (P.twoOmegaFive_component structural modules escape natural) hc
  rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hle] at hi
  exact (IsIrrPlus.subgroupOf_iff _ _ _ hle _).mp hi

/-- The B.5 comparison preserves the original embedded commutators. -/
theorem twoOmegaSpan_commutator
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    ⁅P.twoOmegaSpan,P.five⁆ = ⁅V,P.five⁆ := by
  let H := P.twoCentralizer
  let K := P.five.subgroupOf H
  let M := ⁅V,P.five⁆.subgroupOf H
  have hMH : ⁅V,P.five⁆ ≤ H :=
    (P.five_moved_le_omegaSpan structural escape).trans P.twoOmegaSpan_le_pointCentralizer
  let : Group.IsPerfect P.five := Chapter1.mem_L_isPerfect (P.five_local_family structural)
  let e := P.twoOmegaFiveEquiv structural escape
    (P.two_source_normalizes structural modules escape natural)
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
    rw [←P.five_omega_commutator structural escape] at hz
    apply P.five_moves_six structural escape
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
      (centralizer_le (Set.singleton_subset_iff.mpr P.six_mem_omega))
  have hle := NormalElementaryQuotient.commutator_le_of_noncentral_invariant
    P.twoOmegaModule M K (fun _ hx => P.five_moved_le_omegaSpan structural escape hx)
    hn P.twoOmegaMap (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (P.twoOmegaFive_moved_irrPlus structural modules escape natural) hm
  have hh := Subgroup.map_mono (f := H.subtype) hle
  rw [map_commutator,map_subgroupOf_eq_of_le P.twoOmegaSpan_le_pointCentralizer,
    map_subgroupOf_eq_of_le P.five_le_twoCentralizer,map_subgroupOf_eq_of_le hMH] at hh
  exact P.two_omegaSpan_commutator_eq_of_le structural escape hh

end SylowNormalizer.Points
namespace PointCentralizers

/-- All component and moved-module premises of the weight-two input are discharged. -/
theorem source_twoInput (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    TwoInput P := by
  have hn := P.two_source_normalizes structural modules escape natural
  exact ⟨hn,P.two_section_fixes_moved_of_normalizes structural
    ((ChapterA.Section04.twoSectionCentralizer_le _ _).trans
      (P.two_moved_normalized_of_omegaSpan_commutator hn
        (P.twoOmegaSpan_commutator structural modules escape natural)))⟩

/-- Source 12.3.6–8 supplies the exact point-centralizer input to LocalAnalysis. -/
theorem source_pointCentralizers (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (v : V) (hv : v ≠ 1)
    (hw : BinarySevenCode.weight (E.coordinates v).toAdd.val = 2 ∨
      BinarySevenCode.weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) :=
  pointCentralizers P (source_sixInput P structural)
    (source_twoInput P structural modules escape natural) structural v hv hw

/-- The completed point-centralizer argument feeds the original local-analysis consumer. -/
def source_localAnalysis (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    S.LocalAnalysis :=
  localAnalysis_of_twoInput P structural (source_twoInput P structural modules escape natural)

end PointCentralizers
namespace Setup.NaturalCoordinates
variable (E : S.NaturalCoordinates)

/-- Central representatives of both source point orbits in the original module. -/
def sourcePoints
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) : SylowNormalizer.Points E := by
  let ht := E.central_representative_weight structural (n := 2) (Or.inl rfl)
  let hs := E.central_representative_weight structural (n := 6) (Or.inr (Or.inr rfl))
  exact ⟨ht.choose,hs.choose,ht.choose_spec.1,hs.choose_spec.1,
    ht.choose_spec.2,hs.choose_spec.2⟩

/-- The ambient bound for every nonidentity point of weight two or six,
with no choice of representatives or local module premise left to the caller. -/
theorem source_point_centralizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (v : V) (hv : v ≠ 1)
    (hw : BinarySevenCode.weight (E.coordinates v).toAdd.val = 2 ∨
      BinarySevenCode.weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) :=
  PointCentralizers.source_pointCentralizers (E.sourcePoints structural)
    structural modules escape natural v hv hw

/-- The completed local analysis from the task's precise source inputs.
The final 12.3.1 owner supplies uniform natural coordinates. -/
def source_localAnalysis
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    S.LocalAnalysis :=
  PointCentralizers.source_localAnalysis (E.sourcePoints structural)
    structural modules escape natural

end Setup.NaturalCoordinates
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
