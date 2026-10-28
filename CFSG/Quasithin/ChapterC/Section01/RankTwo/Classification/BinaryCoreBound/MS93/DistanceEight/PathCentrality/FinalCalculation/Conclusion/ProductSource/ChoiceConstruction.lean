module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.ChoiceConstruction.LocalChoice

/-!
# Constructing the two selected critical pairs in MS93 (4.4)

The natural-module calculation supplies two incident edge subgroups with
the source avoidance and intersection clauses. Apply prescribed replacement
to the regular central window. Define beta and delta as the images of the
two original vertices under the same returned conjugator, so incidence is
retained even though replacement identifies only the edge subgroups.

The final theorem applies this constructed pair to the existing selected
commutator calculation and proves that the literal terminal product has
order four. Only the preceding source callbacks remain explicit.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), conclusion of (4.4), printed p.895 after (4.4.5).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Construct the two incident, separated critical choices on printed p.895.
The selected neighbors are images under the actual replacement conjugators;
only their edge subgroups are identified with the initial geometric choices. -/
theorem selectedPair_nonempty (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    Nonempty (SelectedPair e) := by
  let p := e.window 4 (by decide) (by decide)
  have hreg : HasTurnConjugators R p := e.window_regular 4 (by decide) (by decide)
  have ht : Adjacent R (e.walk.getVert 4) (e.walk.getVert 5) := path_adjacent e 4 (by omega)
  obtain ⟨t₁, t₂, ht₁, ht₂, hav₁, hav₂, hn₁, hn₂, hsep⟩ :=
    ChoiceConstruction.incident_choices common p ht
  have make (t : Vertex R) (ht : Adjacent R (e.walk.getVert 4) t)
      (hav : ¬ ⁅Z R (e.walk.getVert 4), Z R (e.walk.getVert (4 + geometry.b R))⁆ ≤
        edgeCommutator R (e.walk.getVert 4) t)
      (hn : ¬ Z R (e.walk.getVert (4 + geometry.b R)) ≤
        stabilizer R (e.walk.getVert 4) ⊓
          normalizer (edgeCommutator R (e.walk.getVert 4) t : Set (FreeAmalgam R))) :
      ∃ s : SelectedVertex e, edgeCommutator R a s.beta = edgeCommutator R a t := by
    obtain ⟨g, hg, he, ⟨q⟩⟩ := PrescribedReplacement.exists_critical_path (R := R) (p := p)
      (replacement p hreg) (by omega) ht hn
    have hp1 : p.walk.getVert 1 = e.walk.getVert 5 :=
      e.window_getVert 4 (by decide) (by decide) 1 (by omega)
    have hp2 : p.walk.getVert 2 = e.walk.getVert 6 :=
      e.window_getVert 4 (by decide) (by decide) 2 (by omega)
    have hpend : p.walk.getVert (p.walk.length - 2) = e.walk.getVert (2 + geometry.b R) := by
      rw [p.length_eq_b, e.window_getVert 4 (by decide) (by decide) _ (by omega)]
      congr 1
      omega
    have hga : g ∈ stabilizer R a := e.center_eq ▸ hg
    have hedge : edgeCommutator R a (act R g (e.walk.getVert 5)) = edgeCommutator R a t := by
      have h := RegularPaths.edgeCommutator_act g a (e.walk.getVert 5)
      rw [show act R g a = a from hga] at h
      rw [hp1, e.center_eq] at he
      exact h.trans he
    have hq : CriticalPath R geometry (act R g (e.walk.getVert 6))
        (e.walk.getVert (2 + geometry.b R)) := by
      rwa [hp2, hpend] at q
    let s : SelectedVertex e := {
      beta := act R g (e.walk.getVert 5)
      delta := act R g (e.walk.getVert 6)
      conjugator := g
      mem_stabilizer := hga
      beta_eq := rfl
      delta_eq := rfl
      critical := hq
      avoids := by
        rw [hedge]
        simpa only [e.center_eq] using hav }
    exact ⟨s, hedge⟩
  obtain ⟨s₁, hs₁⟩ := make t₁ ht₁ hav₁ hn₁
  obtain ⟨s₂, hs₂⟩ := make t₂ ht₂ hav₂ hn₂
  refine ⟨⟨s₁, s₂, ?_⟩⟩
  rw [hs₁, hs₂]
  simpa only [e.center_eq] using hsep

/-- Apply the constructed source pair to the previously proved Ri product
calculation, retaining only the preceding source callbacks. -/
theorem terminalProduct_card_of_source_choices (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    Nat.card (terminalProduct e) = 4 := by
  obtain ⟨pair⟩ := selectedPair_nonempty common hb replacement e
  exact pair.terminalProduct_card common hb hlocal sections
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
