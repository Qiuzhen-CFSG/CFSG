module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CenterComparison.Reciprocal
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes.Comparison
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization.Consumers

/-!
# Original G₂ weak closure with the covering centers retained

The full reciprocal-root family gives mutual normalization when the covering
center is nonzero. Single-commutator comparison then identifies both centers;
the zero-center case is immediate. This absorbs the reciprocal center into
every original root plane. Component uniqueness and generation by these
planes identify L with Lᵍ, contradicting noncentrality inside the elementary
full M-module. Hence W₀(T,V) centralizes V. The existing localization proves
the remaining normalizer and R₁-centralizer clauses and their rank-one consumer.

Only the permitted preceding maximal-local uniqueness, third-space
centralizer, fixed-line and component-uniqueness clauses remain explicit.
Their discharge belongs to qt-d-1222-natural-local-geometry. No RootSpan.moved
or fixed-space vanishing is used. Source: Aschbacher--Smith 11.2.2(5--6)
and 11.5.1, printed pp.768,778.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Atlas.G2 Atlas.G2.Natural Atlas.SplitOctonion Atlas.G2.Explicit
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CenterComparison
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))

variable (f : InvariantFlag (Coordinates.g2 m))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))

include hunique hthree hline in
/-- The actual source pair has equal full covering centers, including the
nontrivial nonsplit central-extension branch. -/
theorem source_covering_centers_eq (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hnon : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    (V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
      V ⊓ centralizer (L : Set G) := by
  by_cases hc : V ⊓ centralizer (L : Set G)=⊥
  · rw [hc,Subgroup.map_bot]
  obtain ⟨u,a,hact,-,ha,hroots⟩ :=
    ReciprocalRoots.source_root_family D S m f hunique hthree hline g hg hnon
  have hp := Parameters.source_parameters D S f hunique hthree hline
  have hn := CentralContainment.normalizes_conjugate_of_central_ne_bot D S
    (ActorRecognition.recentered D S m u) hunique hc hp.1
    (RootPullback.strict_globalR_of_preceding D S m f hunique hthree hline)
    g a hact hroots
  exact covering_centers_eq D S (ActorRecognition.recentered D S m u)
    hp.2.2.1.2 g (hg.trans S.sylow_normalizes) hn hnon a hact ha

variable (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
    (f.Vi 1) (localResidual L (f.Vi 1)))

include hunique hthree hline hcomponent in
/-- Original 11.2.2(5): the zeroth weak closure centralizes the entire V,
with no condition on its covering center. -/
theorem source_zero_centralizes :
    indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  refine le_inf (indexedWeakClosure_le V (T : Subgroup G) 0) ?_
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g,rfl,hg⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
  by_contra hnon
  have hcomm : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro he
    exact hnon (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans he))
  obtain ⟨u,a,hact,-,ha,hroots⟩ :=
    ReciprocalRoots.source_root_family D S m f hunique hthree hline g hg hcomm
  have hcenters := source_covering_centers_eq D S m f hunique hthree hline g hg hcomm
  have hgM := CommonPlanes.mem_normalizer_of_covering_center_absorption D S m f
    hcomponent u g a hact ha hroots (fun v _ => by
      rw [hcenters,←(Coordinates.g2 (ActorRecognition.recentered D S m u)).preimage_bot]
      exact ((Coordinates.g2 (ActorRecognition.recentered D S m u)).preimage_le_iff _ _).mpr bot_le)
  let W := componentOrbit V (normalizer (L : Set G))
  let : IsElementaryAbelian 2 W := Preliminary.fullModule_elementary D S
  have hVW : V ≤ W := le_componentOrbit V _
  have hAW : V.map (MulAut.conj g).toMonoidHom ≤ W :=
    le_iSup_of_le (⟨g,hgM⟩ : normalizer (L : Set G)) le_rfl
  exact hnon (hAW.trans ((Subgroup.le_centralizer W).trans (Subgroup.centralizer_le hVW)))

include hunique hthree hline hcomponent in
/-- Original G₂ 11.2.2(5--6), on the original flag, R₁ and full module. -/
theorem source_clauses :
    indexedWeakClosure V (T : Subgroup G) 0 ≤
        (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ normalizer (L : Set G) ∧
      0 < globalW V (T : Subgroup G) ∧
      centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G) ∧
      indexedWeakClosure V (f.Ri 0) 0 = indexedWeakClosure V (T : Subgroup G) 0 ∧
      normalizer (indexedWeakClosure V (f.Ri 0) 0 : Set G) ≤ normalizer (L : Set G) := by
  have hw := source_zero_centralizes D S m f hunique hthree hline hcomponent
  obtain ⟨hN,hwpos,heq,hNR⟩ := normalizer_bounds_of_zero_centralizes D S f hw
  exact ⟨hw,hN,hwpos,Localization.source_clause_six_of_preceding D S m f hunique hthree hline,
    heq,hNR⟩

include hunique hthree hline hcomponent in
/-- The literal rank-one R₁ consumer, now with all G₂ closure premises proved. -/
theorem rankOne_impossible
    (H₁ : Subgroup G) (P : Sylow 2 H₁)
    (hP : (P : Subgroup H₁).map H₁.subtype = f.Ri 0)
    (hn : generationParameter H₁ = 1) (hout : ¬ H₁ ≤ normalizer (L : Set G)) : False :=
  Localization.rankOne_impossible_of_preceding_and_zero_centralizes D S m f hunique hthree hline
    (source_zero_centralizes D S m f hunique hthree hline hcomponent) H₁ P hP hn hout

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CenterComparison
