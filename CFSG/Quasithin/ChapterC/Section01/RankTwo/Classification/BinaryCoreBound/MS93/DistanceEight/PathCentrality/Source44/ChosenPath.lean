module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.PredecessorKernel

/-!
# The source factor input from one selected regular configuration

A single extended path and its two separated critical replacements determine
all the numerical, natural-section and centrality conclusions of MS93 (4.4).
Those conclusions give index four on every incident edge. Independently, the
source failed-span calculation shows that failure of the remaining image-two
normalization would force index eight. This recovers prescribed replacement
for every regular critical path after proving the index, and fills `Earlier`
without assuming universal replacement at the start.

The final equivalence isolates the finite source construction still needed:
one literal length-b+8 path carrying the five critical windows, together with
the two same-conjugator choices of printed p.895. This module does not assert
existence of that configuration from CommonFacts alone. Its original-input
consumer uses the actual characteristic reduction and subgroup inclusion.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.4)--(4.4.5) and the
conclusion of (4.4), printed pp.894--895; (4.5.1), printed p.896.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.ChosenPath
open PathCentrality.RegularPaths PathCentrality.RegularPaths.CommutatorPropagation
open FinalCalculation FinalCalculation.Conclusion
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- An index-four edge excludes the only remaining image-two obstruction.
The hypothesis is a local index bound, independently of an `Earlier` record. -/
theorem two_image_normalization_of_edge_index_le_four
    (common : CommonFacts R source geometry)
    (hindex : ∀ c t, color R c = false → Adjacent R c t →
      (Q R c).relIndex (Q R t) ≤ 4) :
    Replacement.SourceCritical.FailedSpanTwoImageNormalization R geometry := by
  intro a a' p hp t ht hne g hg hge hfail
  by_contra hnorm
  obtain ⟨n, hn, hlen, hforward, hfixed, htwo, hedge, hprev, hfailure⟩ :=
    Replacement.PredecessorKernel.failed_span_two_image_failure common p hp ht hne hg hge
      hfail hnorm
  let j := p.walk.length - 4 * n
  have hjlen : j ≤ p.walk.length := Nat.sub_le _ _
  have hj : 4 ≤ j := by dsimp only [j]; omega
  have heven : Even j := by
    have hh : Even p.walk.length := by
      rw [p.length_eq_b]
      exact geometry.even (alpha R) rfl
    dsimp only [j]
    rw [Nat.even_iff] at hh ⊢
    omega
  have hc := (p.vertex_color hjlen).mpr heven
  have hs : Adjacent R (p.walk.getVert j) (p.walk.getVert (j - 1)) := by
    apply adjacent_symm R
    have h := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := j - 1) (by omega))
    rwa [show j - 1 + 1 = j by omega] at h
  have hi := hindex _ _ hc hs
  change (Q R (p.walk.getVert j)).relIndex (Q R (p.walk.getVert (j - 1))) = 8 at hedge
  omega

/-- Recover every regular prescribed replacement after the edge bound is known. -/
theorem replacement_of_edge_index_le_four
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hindex : ∀ c t, color R c = false → Adjacent R c t →
      (Q R c).relIndex (Q R t) ≤ 4)
    {a a'} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    PrescribedReplacement R p :=
  Replacement.SourceCritical.prescribedReplacement_of_two_image_normalized common hb
    (two_image_normalization_of_edge_index_le_four common hindex) p hp

/-- One genuine source-selected configuration supplies all preceding factor inputs.
The universal replacement field is derived after the numerical edge calculation. -/
theorem earlier_of_selected_path
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a : Vertex R} (e : ExtendedPath geometry a) (pair : ProductSource.SelectedPair e) :
    CoreFactors.Earlier R geometry := by
  have hsix := RegularSource.six_lt common hb
  have hn := fun c hc => SourceEarlier.Radius.natural_section common hsix e (c := c) hc
  have hprefix := RegularSource.criticalPrefixControl common hb
  obtain ⟨hd,hc,hi⟩ := ProductEstimates.conclusions common hsix hn e
    (SourceEarlier.Product.selected_card pair common hsix hprefix hn)
    (SourceEarlier.Product.terminalProduct_le_fixed hsix hprefix e)
    (fun hlarge => SourceEarlier.Product.first_edge common hlarge hprefix hn e pair)
  have replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p :=
    replacement_of_edge_index_le_four common hb (fun c t hc ht => (hi c t hc ht).2.le)
  exact {
    distance := hd
    natural_section := hn
    centrality := hc
    edge_Z_index := fun c t hc ht => (hi c t hc ht).1
    edge_Q_index := fun c t hc ht => (hi c t hc ht).2
    extended := RegularSource.extended_of_replacement common hb replacement
    replacement := fun _ _ p hp => replacement p hp }

/-- Exact finite existence target for an alternate construction of the source factors. -/
theorem earlier_iff_selected_path
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    Nonempty (CoreFactors.Earlier R geometry) ↔
      ∃ e : ExtendedPath geometry (alpha R), Nonempty (ProductSource.SelectedPair e) := by
  constructor
  · rintro ⟨earlier⟩
    obtain ⟨e⟩ := earlier.extended (alpha R) rfl
    exact ⟨e, ProductSource.selectedPair_nonempty common (by rw [earlier.distance]; decide)
      (fun p hp => earlier.replacement _ _ p hp) e⟩
  · rintro ⟨e, ⟨pair⟩⟩
    exact ⟨earlier_of_selected_path common hb e pair⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.ChosenPath

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {L T : Subgroup J} {h : Input κ L T} (t : InputSetup h)
open DistanceEight.PathCentrality DistanceEight.PathCentrality.Source44

/-- The original characteristic-replacement four-group from the finite source
configuration. No additional normalizer or universal replacement input occurs. -/
theorem reducedCentralFour_of_selected_path
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    {a : Vertex t.reduction.radical}
    (e : RegularPaths.ExtendedPath t.geometry a)
    (pair : FinalCalculation.Conclusion.ProductSource.SelectedPair e) :
    Nat.card t.reducedCentralFour = 4 ∧ IsElementaryAbelian 2 t.reducedCentralFour ∧
      t.reducedCentralFour ≤ commutatorCore L ∧
      t.reducedCentralFour ≤ centralizer (L : Set J) := by
  have earlier := ChosenPath.earlier_of_selected_path common hb e pair
  exact ⟨t.reducedCentralFour_card common earlier,
    t.reducedCentralFour_elementary common earlier,
    t.reducedCentralFour_le_commutatorCore common earlier,
    t.reducedCentralFour_centralizes_component earlier⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
