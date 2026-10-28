module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.ChoiceConstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductEstimates.SourceCompletion

/-!
# The selected-product estimates from the preceding MS93 source inputs

Construct the two separated critical choices by the finite natural-module
argument and prescribed replacement. Their nonzero commutators have trivial
intersection and fill the literal terminal product, which has order four.
This gives its equality with the predecessor edge at indices (b, b-1).
Local commutator control gives its fixed-core bound at b-2 independently.
For b>8, the checked natural-centralizer comparison identifies the same
product with the first edge.

The final applications discharge the SelectedPair premise in SourceCompletion
and retain only the permitted preceding source inputs: the actual extended
path, full local commutator control, prescribed replacement on regular paths,
and the full natural sections. Their earlier-source construction belongs to
the PathCentrality and FinalCalculation assembly owners. No selection,
kernel-comparison, moving-edge fixation or final numerical conclusion is an
input here. This leaf avoids an import cycle with the lower ProductSource
and ProductEstimates modules; the final Conclusion owner can import it directly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), conclusion of (4.4), printed p.895 after (4.4.5).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.OriginalSource
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The literal terminal product has order four, with the geometric choices
constructed from the prescribed replacement on regular critical paths. -/
theorem terminalProduct_card (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    Nat.card (terminalProduct e) = 4 :=
  terminalProduct_card_of_source_choices common hb hlocal replacement sections e

omit [Finite M] in
/-- The fixed-core estimate uses the actual retained turn and full local
commutator control; it does not require finite M or geometric selection. -/
theorem terminalProduct_le_fixed (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2)) :=
  ProductSource.terminalProduct_le_fixed hb hlocal e

/-- The source identifies the product with the predecessor edge (b, b-1). -/
theorem terminalProduct_eq_backward_edge (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    terminalProduct e = edgeCommutator R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) :=
  terminalProduct_eq_backward_edge_of_card common hb e
    (terminalProduct_card common hb hlocal replacement sections e)

/-- Only the b>8 branch requires the first-edge equality. The actual selected
pair retains the natural-kernel containment used by the internal comparison. -/
theorem terminalProduct_eq_first_edge (common : CommonFacts R source geometry)
    (hb : 8 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    terminalProduct e = edgeCommutator R a (e.walk.getVert 5) := by
  obtain ⟨p⟩ := selectedPair_nonempty common (by omega) replacement e
  exact ProductEstimates.SourceCompletion.first_edge common hb hlocal sections e p

/-- The constructed choices realize the source's literal setwise product
of two nonzero, disjoint selected commutators. No Ri estimate is assumed. -/
theorem exists_selected_product (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    ∃ p : SelectedPair e,
      selectedCommutator e p.left.delta ≠ ⊥ ∧
      selectedCommutator e p.right.delta ≠ ⊥ ∧
      selectedCommutator e p.left.delta ⊓ selectedCommutator e p.right.delta = ⊥ ∧
      (↑(terminalProduct e) : Set (FreeAmalgam R)) =
        (↑(selectedCommutator e p.left.delta) : Set (FreeAmalgam R)) *
          (↑(selectedCommutator e p.right.delta) : Set (FreeAmalgam R)) := by
  obtain ⟨p⟩ := selectedPair_nonempty common hb replacement e
  exact ⟨p, p.left.commutator_ne_bot common hb sections,
    p.right.commutator_ne_bot common hb sections,
    p.commutators_inf_eq_bot common hb hlocal,
    p.terminalProduct_eq_mul common hb hlocal sections⟩

/-- Apply the completed source choices to all concluding (4.4) outputs:
distance eight, centrality in the whole stabilizer, and both exact indices. -/
theorem conclusions (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    geometry.b R = 8 ∧
      (∀ c, color R c = false → ⁅V R c, Q R c⁆ ≤
        (center (stabilizer R c)).map (stabilizer R c).subtype) ∧
      (∀ c t, color R c = false → Adjacent R c t →
        (Z R t).relIndex (Z R c) = 2 ∧ (Q R c).relIndex (Q R t) = 4) := by
  obtain ⟨p⟩ := selectedPair_nonempty common hb replacement e
  exact ProductEstimates.SourceCompletion.conclusions common hb hlocal sections e p

/-- The original alpha,beta application with every selected-product premise
discharged and the earlier source callbacks still explicit. -/
theorem alpha_beta (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    geometry.b R = 8 ∧
      ⁅V R (alpha R), Q R (alpha R)⁆ ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype ∧
      (Z R (beta R)).relIndex (Z R (alpha R)) = 2 ∧
      (Q R (alpha R)).relIndex (Q R (beta R)) = 4 := by
  obtain ⟨p⟩ := selectedPair_nonempty common hb replacement e
  exact ProductEstimates.SourceCompletion.alpha_beta common hb hlocal sections e p

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.OriginalSource
