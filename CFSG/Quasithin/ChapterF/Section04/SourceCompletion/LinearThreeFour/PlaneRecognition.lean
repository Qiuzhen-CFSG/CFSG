module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.PlaneRecognition.Model
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.PlaneRecognition.Coordinates
public import Theory.GroupAction.RankTwoCosetGeometry.IncidenceTransport
public import Theory.SpecificGroups.PSL3Four.Collineations.PerfectImage

/-!
# Recognition of the completion from its order-four plane geometry

The actual typed coset plane has coordinates in PG(2,4), by the elementary
uniqueness proof for planes of order four. Conjugating the original incidence
action by these coordinates gives a homomorphism into the full collineation
group. The completion is perfect, and the collineation quotient by the actual
PSL image is solvable, so the action lands in PSL₃(4).

The resulting type-preserving equivariant graph isomorphism feeds the published
geometric reduction, which proves injectivity, surjectivity and simultaneous
alignment of the two endpoint ranges. The final recognition theorem assumes
exactly the whole-overlap identity, unique geodesics below three, diameter at
most three, and valence five. Earlier conditional coordinate APIs are retained.

This completes the plane-action branch used in the PSL₃(4) case of
Aschbacher–Smith F.4.8(2), printed p.278, and F.4.26, printed p.288. It is not
an unconditional F.4.26 theorem: the separate smallness argument must supply
the geometric premises from the original involutions.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
open Configuration Subgroup.CosetGeometry Matrix.PSL3Four
local instance : DecidableEq F := Classical.decEq _
variable {G : Type*} [Group G] (c : Completion G)
variable (ep : c.Point ≃ PG) (el : c.Line ≃ PG)
  (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l)

/-- The original paired coset action, conjugated by the two incidence coordinates. -/
def actionInCoordinates : G →* Collineation PG PG :=
  (Collineation.transport ep el hi).comp c.planeAction

/-- Perfectness of the actual transported image follows from the marked local groups. -/
theorem coordinate_image_isPerfect : Group.IsPerfect (c.actionInCoordinates ep el hi).range := by
  let := c.isPerfect
  exact Group.IsPerfect.range _

/-- Perfectness of the literal completion excludes the solvable outer quotient
of the coordinate plane's full incidence group. -/
theorem actionInCoordinates_mem_pslCollineation (g : G) :
    c.actionInCoordinates ep el hi g ∈ pslCollineation.range := by
  let := c.isPerfect
  exact perfect_hom_mem_pslCollineation (c.actionInCoordinates ep el hi) g

variable (hlinear : ∀ g, c.actionInCoordinates ep el hi g ∈ pslCollineation.range)

private def linearCoordinateHom : G →* PSL :=
  (MonoidHom.ofInjective pslCollineation_injective).symm.toMonoidHom.comp
    ((c.actionInCoordinates ep el hi).codRestrict pslCollineation.range hlinear)

private theorem pslCollineation_linearCoordinateHom (g : G) :
    pslCollineation (c.linearCoordinateHom ep el hi hlinear g) =
      c.actionInCoordinates ep el hi g :=
  congrArg Subtype.val ((MonoidHom.ofInjective pslCollineation_injective).apply_symm_apply
    ⟨c.actionInCoordinates ep el hi g, hlinear g⟩)

include ep el hi hlinear

/-- Incidence coordinates whose actual transported action lands in PSL give the
required equivariant graph comparison. The coordinate and image premises remain explicit. -/
theorem exists_equivariant_graphIso_of_linear_coordinates :
    ∃ (q : c.graph ≃g modelCompletion.graph) (f : G →* PSL),
      (∀ v, (q v).type = v.type) ∧ (∀ g v, q (g • v) = f g • q v) := by
  let f := c.linearCoordinateHom ep el hi hlinear
  let ep' := ep.trans (modelCoordinates false).symm
  let el' := el.trans (modelCoordinates true).symm
  have hi' (p : c.Point) (l : c.Line) : ep' p ∈ el' l ↔ p ∈ l := by
    rw [← modelCoordinates_incidence]
    simpa only [ep', el', Equiv.trans_apply, Equiv.apply_symm_apply] using hi p l
  have hp' (g : G) (p : c.Point) : ep' (g • p) = f g • ep' p := by
    apply (modelCoordinates false).injective
    have h := congrArg (fun a : Collineation PG PG => Collineation.pointHom PG PG a (ep p))
      (c.pslCollineation_linearCoordinateHom ep el hi hlinear g)
    simp only [actionInCoordinates, MonoidHom.comp_apply, Collineation.transport_point,
      planeAction, Collineation.ofAction_point, Equiv.symm_apply_apply,
      pslCollineation_point] at h
    simpa only [ep', Equiv.trans_apply, modelCoordinates_point_smul,
      Equiv.apply_symm_apply] using h.symm
  have hl' (g : G) (l : c.Line) : el' (g • l) = f g • el' l := by
    apply (modelCoordinates true).injective
    have h := congrArg (fun a : Collineation PG PG => Collineation.lineHom PG PG a (el l))
      (c.pslCollineation_linearCoordinateHom ep el hi hlinear g)
    simp only [actionInCoordinates, MonoidHom.comp_apply, Collineation.transport_line,
      planeAction, Collineation.ofAction_line, Equiv.symm_apply_apply] at h
    simpa only [el', Equiv.trans_apply, modelCoordinates_line_action,
      Equiv.apply_symm_apply] using h.symm
  exact ⟨RankTwo.graphIsoOfIncidence c.family modelCompletion.family ep' el' hi', f,
    RankTwo.graphIsoOfIncidence_type c.family modelCompletion.family ep' el' hi',
    RankTwo.graphIsoOfIncidence_equivariant c.family modelCompletion.family ep' el' hi' f hp' hl'⟩

/-- Apply the published kernel and simultaneous endpoint alignment reduction to
the graph comparison obtained from actual linear plane coordinates. -/
theorem exists_parabolic_preserving_equiv_of_linear_coordinates
    (ho : c.left.range ⊓ c.right.range = c.middle.range) :
    ∃ e : G ≃* PSL,
      c.left.range.map e.toMonoidHom = Matrix.PSL3.LinearThree.pointParabolic F ∧
      c.right.range.map e.toMonoidHom = Matrix.PSL3.LinearThree.lineParabolic F := by
  obtain ⟨q, f, ht, he⟩ := c.exists_equivariant_graphIso_of_linear_coordinates ep el hi hlinear
  exact c.exists_parabolic_preserving_equiv_of_equivariant_graphIso ho q f ht he

omit hlinear in
/-- Incidence coordinates alone give the comparison into the actual PSL₃(4).
There is no additional assumption on the transported action. -/
theorem exists_equivariant_graphIso_of_coordinates :
    ∃ (q : c.graph ≃g modelCompletion.graph) (f : G →* PSL),
      (∀ v, (q v).type = v.type) ∧ (∀ g v, q (g • v) = f g • q v) :=
  c.exists_equivariant_graphIso_of_linear_coordinates ep el hi
    (c.actionInCoordinates_mem_pslCollineation ep el hi)

omit hlinear in
/-- Apply the published geometric reduction with the PSL-image premise
discharged. Only the incidence coordinates and whole overlap remain explicit. -/
theorem exists_parabolic_preserving_equiv_of_coordinates
    (ho : c.left.range ⊓ c.right.range = c.middle.range) :
    ∃ e : G ≃* PSL,
      c.left.range.map e.toMonoidHom = Matrix.PSL3.LinearThree.pointParabolic F ∧
      c.right.range.map e.toMonoidHom = Matrix.PSL3.LinearThree.lineParabolic F := by
  obtain ⟨q, f, ht, he⟩ := c.exists_equivariant_graphIso_of_coordinates ep el hi
  exact c.exists_parabolic_preserving_equiv_of_equivariant_graphIso ho q f ht he

omit ep el hi hlinear in
/-- The geometric premises determine the completion's order, using the actual
point cosets and the already established endpoint order. -/
theorem card_of_plane_geometry [Finite G]
    (hu : c.graph.UniqueGeodesicsBelow 3) (hd : ∀ v w, c.graph.dist v w ≤ 3)
    (hv : ∀ v, Nat.card (c.graph.neighborSet v) = 5) : Nat.card G = 20160 := by
  have hi : c.left.range.index = 21 := by
    rw [Subgroup.index_eq_card]
    exact (Nat.card_congr (RankTwo.fiberEquivQuotient c.family false)).symm.trans
      (c.card_points_of_geometry hu hd hv)
  have hc := c.left.range.card_mul_index
  rw [c.left_card_eq, hi] at hc
  exact hc.symm

omit ep el hi hlinear in
/-- The order-four geometry gives a type-preserving equivariant comparison with
the literal PSL₃(4) model. Perfectness of the local completion discharges the
PSL-image condition; no additional action or group hypothesis is required. -/
theorem exists_equivariant_graphIso_of_plane_geometry [Finite G]
    (hu : c.graph.UniqueGeodesicsBelow 3) (hd : ∀ v w, c.graph.dist v w ≤ 3)
    (hv : ∀ v, Nat.card (c.graph.neighborSet v) = 5) :
    ∃ (q : c.graph ≃g modelCompletion.graph) (f : G →* PSL),
      (∀ v, (q v).type = v.type) ∧ (∀ g v, q (g • v) = f g • q v) := by
  obtain ⟨ep,el,hi⟩ := c.exists_coordinates_of_geometry hu hd hv
  exact c.exists_equivariant_graphIso_of_coordinates ep el hi

omit ep el hi hlinear in
/-- Recognition with exactly the whole-overlap, short-geodesic uniqueness,
diameter-three and valence-five premises. The published geometric reduction
supplies faithfulness, surjectivity and simultaneous endpoint alignment. -/
theorem exists_parabolic_preserving_equiv_of_plane_geometry [Finite G]
    (ho : c.left.range ⊓ c.right.range = c.middle.range)
    (hu : c.graph.UniqueGeodesicsBelow 3) (hd : ∀ v w, c.graph.dist v w ≤ 3)
    (hv : ∀ v, Nat.card (c.graph.neighborSet v) = 5) :
    ∃ e : G ≃* PSL,
      c.left.range.map e.toMonoidHom = Matrix.PSL3.LinearThree.pointParabolic F ∧
      c.right.range.map e.toMonoidHom = Matrix.PSL3.LinearThree.lineParabolic F := by
  obtain ⟨q,f,ht,he⟩ := c.exists_equivariant_graphIso_of_plane_geometry hu hd hv
  exact c.exists_parabolic_preserving_equiv_of_equivariant_graphIso ho q f ht he

end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
