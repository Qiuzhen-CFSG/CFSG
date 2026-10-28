module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.ProductFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.ProductSelected
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.ChoiceConstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductEstimates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.Reduction

/-!
# The concluding MS93 outputs from the actual critical-prefix input

Prescribed replacement constructs the separated selected pair. Its two
commutators fill the terminal product of order four, while the radius-four
actor proof puts that product in the fixed core. These estimates give
moving-edge fixation. If b exceeds eight, the forward edge fills the
proper natural centralizer, identifying it with the same terminal product.
The existing concluding calculation now gives distance eight, centrality
in every M-vertex stabilizer and both literal edge indices.

Only critical-prefix local control, the preceding full natural sections,
prescribed replacement and the actual extended path are inputs here.
Source: Meierfrankenfeld--Stellmacher (1993), conclusion of (4.4), p.895.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.Product
open FinalCalculation FinalCalculation.Conclusion
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The forward-edge identity for the large-distance branch, retaining
only the actual selected pair and critical-prefix control. -/
theorem first_edge (common : CommonFacts R source geometry)
    (hb : 8 < geometry.b R) (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)))
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    (p : ProductSource.SelectedPair e) :
    terminalProduct e = edgeCommutator R a (e.walk.getVert 5) := by
  have hb6 : 6 < geometry.b R := by omega
  have hcard := selected_card p common hb6 hprefix sections
  have hD := terminalProduct_le_fixed hb6 hprefix e
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
  have hc := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hback : Adjacent R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) := by
    have h := adjacent_symm R (path_adjacent e (geometry.b R - 1) (by omega))
    simpa only [Nat.sub_add_cancel (show 1 ≤ geometry.b R by omega)] using h
  have hEcard : Nat.card E = 4 := by
    apply edge_card_at_all hc ha hback h45
    rw [← ProductSource.terminalProduct_eq_backward_edge_of_card common hb6 e hcard]
    exact hcard
  have hEq : E = C := eq_of_le_of_card_ge hEC (by
    change Nat.card C ≤ Nat.card (edgeCommutator R a (e.walk.getVert 5))
    rw [hEcard]
    exact hCsmall)
  have hQC : Q R (e.walk.getVert (4 + geometry.b R)) ≤ centralizer
      (Z R (e.walk.getVert (4 + geometry.b R)) : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ hy))
  let : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; decide)
  exact eq_of_le_of_card_ge
    ((selected_le_natural_kernel p common hb6 hprefix sections).trans
      ((inf_le_inf_left (U R a) hQC).trans hEq.symm.le))
    (by change Nat.card E ≤ Nat.card (terminalProduct e); rw [hEcard, hcard])

/-- All concluding (4.4) outputs from the original preceding source inputs.
The selected pair is constructed internally by prescribed replacement. -/
theorem conclusions (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
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
  obtain ⟨p⟩ := ProductSource.selectedPair_nonempty common hb replacement e
  exact ProductEstimates.conclusions common hb sections e
    (selected_card p common hb hprefix sections)
    (terminalProduct_le_fixed hb hprefix e)
    (fun hlarge => first_edge common hlarge hprefix sections e p)

/-- The literal alpha,beta consumer of the concluding source calculation. -/
theorem alpha_beta (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
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
  obtain ⟨hd, hc, hi⟩ := conclusions common hb hprefix replacement sections e
  exact ⟨hd, hc _ rfl, hi _ _ rfl (base_adjacent R)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.Product
