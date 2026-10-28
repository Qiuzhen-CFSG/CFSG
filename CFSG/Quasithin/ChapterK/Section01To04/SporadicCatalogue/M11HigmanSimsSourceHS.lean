module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Source
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceGeneration
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Inner
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Inner.FiveRestrictions
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Inner.CoreClosure
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound

/-!
# The inner HS exclusion and the remaining source assembly

The actual HS cover has a two-group center, which disappears in its faithful
irreducible binary action. The proved five-element restrictions and centralizer
closure then give a strict ratio-two gap for every inner elementary actor in
degree twenty. These inputs are discharged here on the original ambient action.

Two substantial representation results remain: degree twenty in the window at
most fifty, and the two outer involution estimates in degree twenty. Their
contracts below are obligations, not assertions. The conditional source assembly
discharges generation, the center bound and all inner calculations, retaining
only those two obligations. In particular it is not `SourceExclusion .hs`.

Source: Aschbacher--Smith, K.4, printed p.457/PDF p.468; Guralnick--Malle,
Classification of 2F-modules I, Proposition 5.1, HS paragraph, preprint pp.16--17,
and Theorem 6.6/Table 6.7. The corrected induced-eight estimate includes regular
rank-three actors and does not use the prose's unsupported cycle-type selection.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory Subgroup Representation.BinaryOffender
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech
universe u v

/-- The original faithful irreducible HS action has binary degree twenty
in the proved degree window. This still requires a representation completeness
proof and field descent; it is not supplied by an FF exclusion. -/
def HigmanSimsDegreeWindow : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V), HigmanSims.SourceHypotheses ρ →
    Module.finrank (ZMod 2) V ≤ 50 → Module.finrank (ZMod 2) V = 20

/-- The degree-twenty estimates for both actual outer involution classes.
The marking is the literal central quotient, and the group remains the
original ambient actor. These estimates are not source hypotheses. -/
def HigmanSimsOuterEstimates : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V), HigmanSims.SourceHypotheses ρ →
    Module.finrank (ZMod 2) V = 20 →
    ∀ e : generalizedFitting G ⧸ center (generalizedFitting G) ≃*
      KnownSimple.SporadicName.hs.Carrier,
    HigmanSims.Twenty.ElementaryOuterEstimates ρ e ∧
      HigmanSims.Twenty.SymmetricOuterEstimates ρ e

variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- All inner estimates in degree twenty, with the cover, order-five
restrictions and actual centralizer-closure construction discharged. -/
theorem higmanSims_inner_estimates (h : HigmanSims.SourceHypotheses ρ)
    (hd : Module.finrank (ZMod 2) V = 20) : HigmanSims.Twenty.InnerEstimates ρ := by
  let := h.quasisimple
  obtain ⟨e⟩ := h.centralQuotient
  exact HigmanSims.Twenty.Inner.estimates_of_inputs h hd
    (Theory.SpecificGroups.J2HSMultipliers.HS.center_isPGroup_of_quotient_equiv e)
    HigmanSims.Twenty.Inner.fiveRestrictions HigmanSims.Twenty.Inner.coreClosureFive

/-- Every inner elementary actor has ratio strictly greater than two in
degree twenty, on the original ambient representation. -/
theorem higmanSims_inner_gap (h : HigmanSims.SourceHypotheses ρ)
    (hd : Module.finrank (ZMod 2) V = 20) {A : Subgroup G}
    (hA : IsElementaryTwo A) (hAL : A ≤ generalizedFitting G) :
    2 * rank A < fixedCodim ρ A :=
  HigmanSims.Twenty.inner_gap_of_estimates h (higmanSims_inner_estimates h hd) hA hAL

/-- A degree-twenty cubic source witness must leave the actual component.
The inner branch has no remaining representation or group-calculation input. -/
theorem higmanSims_cubic_actor_not_le (h : HigmanSims.SourceHypotheses ρ)
    (hd : Module.finrank (ZMod 2) V = 20) {A : Subgroup G}
    (hA : IsElementaryTwo A) (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    ¬ A ≤ generalizedFitting G := by
  intro hAL
  exact (not_lt_of_ge hsmall) (higmanSims_inner_gap h hd hA hAL)

omit [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] in
/-- The full HS source exclusion follows after the independent degree window
and outer estimates are proved. Generation and all inner inputs are discharged. -/
theorem sourceExclusion_hs_of_degree_and_outer
    (hdegree : HigmanSimsDegreeWindow.{u,v})
    (houter : HigmanSimsOuterEstimates.{u,v}) : SourceExclusion.{u,v} .hs := by
  intro G V _ _ _ _ _ ρ h he
  let hs : HigmanSims.SourceHypotheses ρ :=
    ⟨h.sqtk, h.quasisimple, h.faithful, h.irreducible, he⟩
  have hd := hdegree ρ hs (hs.finrank_le_fifty h.cubic_le_two)
  obtain ⟨e⟩ := he
  obtain ⟨hE, hS⟩ := houter ρ hs hd e
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_le_two
  exact (not_lt_of_ge hsmall) (HigmanSims.Twenty.gap_of_estimates hs e
    (higmanSims_inner_estimates hs hd) hE hS A hA)

/-- Transport the conditional HS source assembly through the exact F* equality.
Both substantial remaining inputs stay explicit for final discharge. -/
theorem not_hs_of_rankOne_source_of_degree_and_outer
    (hdegree : HigmanSimsDegreeWindow.{u,v})
    (houter : HigmanSimsOuterEstimates.{u,v}) {L : Subgroup G}
    (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.hs.Carrier)) : False := by
  rcases h.fitting with rfl
  exact sourceExclusion_hs_of_degree_and_outer hdegree houter ρ
    ⟨h.sqtk, h.quasisimple, h.faithful, h.irreducible, h.smallCubic⟩ he

end CFSG.Quasithin.ChapterK.SporadicCatalogue
