module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductEstimates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.Reduction

/-!
# The final MS93 conclusions from the actual selected pair

The selected pair gives the terminal product order four and its containment
in U_alpha intersect Q_(alpha'). Full local commutator control gives the
fixed-core bound independently. The checked symmetric argument therefore
supplies moving-edge fixation without using the first-edge identity.

Apply the genuine (4.2)(i) transfer to put the forward edge in Z_(alpha+1).
It centralizes Q_(alpha+1), which contains Z_(alpha') because the distance
is b-1. This order-four edge fills the proper natural centralizer of
Z_(alpha') in U_alpha. The selected product lies in that centralizer too,
so the already proved product assembly identifies it with the forward edge.
The final consumer now gives distance eight, actual stabilizer centrality
and both source indices, with no separate kernel-comparison premise.

SelectedPair remains an actual source witness: its constructor belongs to
qt-c01-ms93-selected-pair-geometry. The permitted preceding path, local-control
and natural-section inputs retain their existing producers; final discharge
belongs to qt-c01-ms93-conclusion-selected-product and
qt-c01-ms93-final-calculation-conclusion. No assertion about an arbitrary
order-four displacement or a contrary configuration from (4.3) is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4), printed p.895.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductEstimates.SourceCompletion
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The selected product supplies the first-edge identity needed in the b>8
contradiction. Its natural-kernel containment is retained through the actual
SelectedPair assembly; the kernel comparison is proved internally. -/
theorem first_edge (common : CommonFacts R source geometry)
    (hb : 8 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (p : ProductSource.SelectedPair e) :
    terminalProduct e = edgeCommutator R a (e.walk.getVert 5) := by
  have hb6 : 6 < geometry.b R := by omega
  have hcard := p.terminalProduct_card common hb6 hlocal sections
  have hD := ProductSource.terminalProduct_le_fixed hb6 hlocal e
  have hfixed := ProductEstimates.movingEdgeFixed common hb6 sections e hcard hD
  have ha := ExtendedPath.center_color e
  have hy := (e.window 4 (by decide) (by decide)).end_color
  have h45 : Adjacent R a (e.walk.getVert 5) := by
    simpa only [e.center_eq] using path_adjacent e 4 (by omega)
  let E := edgeCommutator R a (e.walk.getVert 5)
  let C := U R a ⊓ centralizer
    (Z R (e.walk.getVert (4 + geometry.b R)) : Set (FreeAmalgam R))
  have hEU : E ≤ U R a := Escape.EdgeTransfer.edge_commutator_le_natural
    common.large_distance (LocalCommutator.moduleFacts common) _ _ ha h45
  have hECQ : E ≤ centralizer (Q R (e.walk.getVert 5) : Set (FreeAmalgam R)) := by
    have hz := Conclusion.edge_le_Z common hfixed ha h45
    rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
      (LocalCommutator.moduleFacts common) _ _ ha h45] at hz
    exact hz.trans inf_le_right
  have hZQ : Z R (e.walk.getVert (4 + geometry.b R)) ≤ Q R (e.walk.getVert 5) := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hy)
    rw [geometry.distance_constant _ hy, SimpleGraph.dist_comm,
      ExtendedPath.distance e (by omega) (by omega)]
    change 4 + geometry.b R - 5 < geometry.b R
    omega
  have hEC : E ≤ C := le_inf hEU (hECQ.trans (centralizer_le hZQ))
  have hCsmall : Nat.card C ≤ 4 := by
    simpa only [e.center_eq] using
      RegularPaths.OrbitEscape.JointNormality.natural_centralizer_card_le_four
        common (e.window 4 (by decide) (by decide))
  let : Finite (U R a) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at a ha]; decide)
  let : Finite C := Finite.of_injective
    (inclusion (show C ≤ U R a from inf_le_left)) (inclusion_injective _)
  apply p.terminalProduct_eq_first_edge_of_kernel_comparison common hb hlocal sections
  intro hEcard
  have hEq : E = C := eq_of_le_of_card_ge hEC (by
    change Nat.card C ≤ Nat.card (edgeCommutator R a (e.walk.getVert 5))
    rw [hEcard]
    exact hCsmall)
  have hQC : Q R (e.walk.getVert (4 + geometry.b R)) ≤ centralizer
      (Z R (e.walk.getVert (4 + geometry.b R)) : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ hy))
  exact (inf_le_inf_left (U R a) hQC).trans hEq.symm.le

/-- Actual final (4.4) application with the selected pair still supplied by its
geometric source owner. All product estimates and the forward comparison are
discharged here; the conclusions retain both literal edge indices. -/
theorem conclusions (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (p : ProductSource.SelectedPair e) :
    geometry.b R = 8 ∧
      (∀ c, color R c = false → ⁅V R c, Q R c⁆ ≤
        (center (stabilizer R c)).map (stabilizer R c).subtype) ∧
      (∀ c t, color R c = false → Adjacent R c t →
        (Z R t).relIndex (Z R c) = 2 ∧ (Q R c).relIndex (Q R t) = 4) :=
  ProductEstimates.conclusions common hb sections e
    (p.terminalProduct_card common hb hlocal sections)
    (ProductSource.terminalProduct_le_fixed hb hlocal e)
    (fun hlarge => first_edge common hlarge hlocal sections e p)

/-- The original alpha,beta consumer with no independent forward-kernel premise.
The actual source SelectedPair remains with its existing geometric constructor. -/
theorem alpha_beta (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (p : ProductSource.SelectedPair e) :
    geometry.b R = 8 ∧
      ⁅V R (alpha R), Q R (alpha R)⁆ ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype ∧
      (Z R (beta R)).relIndex (Z R (alpha R)) = 2 ∧
      (Q R (alpha R)).relIndex (Q R (beta R)) = 4 := by
  obtain ⟨hd, hc, hi⟩ := conclusions common hb hlocal sections e p
  exact ⟨hd, hc _ rfl, hi _ _ rfl (base_adjacent R)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductEstimates.SourceCompletion
