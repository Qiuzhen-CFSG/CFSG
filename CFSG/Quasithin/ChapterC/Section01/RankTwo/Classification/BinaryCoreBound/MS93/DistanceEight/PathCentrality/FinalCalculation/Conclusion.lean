module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.Distance
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.Selected
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductEstimates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductEstimates.SourceCompletion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.SourceAssembly

/-!
# Assembly of the concluding calculations of MS93 (4.4)

`ProductEstimates` derives the symmetric moving-edge bound, local centrality,
both edge indices and the numerical H bound from the selected product's actual
order-four and fixed-core estimates. Its distance-eight conclusion additionally
uses the first-edge equality only when b>8. The product's correct predecessor
edge supplies the adjacent order-four witness. These companions retain the
actual preceding natural sections and extended path.

`ProductSource.OriginalSource` constructs the actual selected pair from
prescribed replacement on regular critical paths and discharges all three
product estimates. Its `conclusions` and `alpha_beta` retain only the preceding
local control, full natural sections and extended path. `SourceAssembly`
also discharges the natural sections using the completed RadiusImage
calculation and supplies the numerical bound |H_alpha| <= 4. The remaining
earlier-source inputs are explicitly documented in that leaf; their production
belongs to the PathCentrality assembly owner.

The historical conditional theorems below remain available, but their
`ProductCalculation` record specifies the wrong successor edge and is not the
original source conclusion. No final core-center conclusion is assumed in
the corrected route.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.895, after (4.4.5).
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Every structural output of (4.4), conditional on its two still-needed
intermediate calculations. The preceding natural-section input retains the
literal quotient action, and centrality is in the whole local stabilizer. -/
theorem conclusions_of_calculations (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hfixed : MovingEdgeFixed geometry)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (product : ProductCalculation e) :
    geometry.b R = 8 ∧
      (∀ c, color R c = false → ⁅V R c, Q R c⁆ ≤
        (center (stabilizer R c)).map (stabilizer R c).subtype) ∧
      (∀ c t, color R c = false → Adjacent R c t →
        (Z R t).relIndex (Z R c) = 2 ∧ (Q R c).relIndex (Q R t) = 4) := by
  refine ⟨distance_eq_eight common hb hfixed e product,
    fun _ hc => centrality_at_all common hfixed sections e hc, ?_⟩
  have hc' := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hat := path_adjacent e (geometry.b R) (by omega)
  have hcard : Nat.card (edgeCommutator R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R + 1))) = 4 := by
    rw [← product.opposite_edge]
    exact product.card
  intro c t hc hct
  exact edge_indices common hfixed hc' hat hcard hc hct

/-- The literal alpha,beta application, including the Z-index lost in OCR. -/
theorem alpha_beta_of_calculations (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hfixed : MovingEdgeFixed geometry)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (product : ProductCalculation e) :
    geometry.b R = 8 ∧
      ⁅V R (alpha R), Q R (alpha R)⁆ ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype ∧
      (Z R (beta R)).relIndex (Z R (alpha R)) = 2 ∧
      (Q R (alpha R)).relIndex (Q R (beta R)) = 4 := by
  obtain ⟨hd, hc, hi⟩ := conclusions_of_calculations common hb hfixed sections e product
  exact ⟨hd, hc _ rfl, hi _ _ rfl (base_adjacent R)⟩

/-- Numerical application at the original alpha even when the supplied path
is centered elsewhere: transport a genuine moving neighbor and its distance. -/
theorem H_alpha_card_le_four_of_moving_edges (common : CommonFacts R source geometry)
    (hfixed : MovingEdgeFixed geometry)
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    Nat.card (H R (alpha R)) ≤ 4 := by
  obtain ⟨d, hd⟩ := exists_moving_neighbor common e (c := alpha R) rfl
  have hspan : Vcirc R (alpha R) ≤ localZSpan R d (alpha R) := by
    rw [localZSpan_eq_conjugates]
    exact Escape.Initial.Natural.moving_generation_of_naturalSection
      source geometry common.large_distance (alpha R) rfl s d hd
  apply Numerical.SourceCenterBound.DistanceGreaterFour.H_card_le_four_of_moving_span
    common rfl (show (cosetGraph R).dist d (alpha R) = 2 by
      rw [SimpleGraph.dist_comm]; exact hd.1) hspan
  exact local_centrality common hfixed rfl s hd

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion
