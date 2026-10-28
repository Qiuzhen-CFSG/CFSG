module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SphereGenerators
/-!
# Propagation of a fixed opposite vertex

An automorphism fixing every neighbor of W and one opposite vertex Y
also fixes every neighbor of Y: two of the four common neighbors with
W determine each remaining point on a line through Y. The connections
inside the opposite sphere generate D, so this local fact propagates
through the entire sphere. Thus the automorphism is the identity.
Source: Aschbacher, Sporadic Groups (1994),45.11, pp.248–249.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

private theorem common_neighbors_not_adj (U I J : c.points)
    (hU : c.collinearity.edist ⟨c.W,c.point_mem⟩ U=2)
    (hI : I∈c.collinearity.commonNeighbors ⟨c.W,c.point_mem⟩ U)
    (hJ : J∈c.collinearity.commonNeighbors ⟨c.W,c.point_mem⟩ U) (hne : I≠J) :
    ¬c.collinearity.Adj I J := by
  intro hij
  obtain ⟨L,hL,hWL,hIL,hJL⟩ := c.triangle_on_line ⟨c.W,c.point_mem⟩ I J hI.1 hJ.1 hij
  exact hne (c.common_neighbors_on_line_unique ⟨c.W,c.point_mem⟩ U I J
    (c.collinearity.edist_eq_two_iff.mp hU).2.1 (c.collinearity.edist_eq_two_iff.mp hU).1
    hI hJ ⟨hL,hWL⟩ hIL hJL)

theorem fixes_opposite_neighbors (f : c.collinearity ≃g c.collinearity)
    (hperp : ∀U:c.points,c.collinearity.Adj ⟨c.W,c.point_mem⟩ U→f U=U)
    (Y : c.points) (hY : c.collinearity.edist ⟨c.W,c.point_mem⟩ Y=2) (hfY : f Y=Y)
    (U : c.points) (hYU : c.collinearity.Adj Y U) : f U=U := by
  by_cases hWU : c.collinearity.Adj ⟨c.W,c.point_mem⟩ U
  · exact hperp U hWU
  have hne : U≠⟨c.W,c.point_mem⟩ := by
    intro he
    exact (c.collinearity.edist_eq_two_iff.mp hY).2.1 (c.collinearity.adj_symm (he ▸ hYU))
  have hU : c.collinearity.edist ⟨c.W,c.point_mem⟩ U=2 := by
    rcases (c.reachable_iff_withinTwo U).mp (c.original_point_reachable U) with he|ha|hd
    · exact (hne he).elim
    · exact (hWU ha).elim
    · exact hd
  obtain ⟨-,hneUY,L,hL,hYL,hUL⟩ := hYU
  obtain ⟨I,hIL⟩ := c.distance_two_common_neighbor_on_each_line hY ⟨L,hL,hYL⟩
  have hIU : c.collinearity.Adj I.val U :=
    ⟨U.property,fun he=>hWU (Subtype.ext he ▸ I.property.1),L,hL,hIL,hUL⟩
  have hI : I.val∈c.collinearity.commonNeighbors ⟨c.W,c.point_mem⟩ U :=
    ⟨I.property.1,c.collinearity.adj_symm hIU⟩
  have hfI : f I.val=I.val := hperp I.val I.property.1
  have hfUY : c.collinearity.Adj Y (f U) := hfY ▸ f.map_rel_iff.mpr (show c.collinearity.Adj Y U from
    ⟨U.property,hneUY,L,hL,hYL,hUL⟩)
  have hfUI : c.collinearity.Adj I.val (f U) := hfI ▸ f.map_rel_iff.mpr hIU
  obtain ⟨L',hL',hYL',hIL',hfUL'⟩ := c.triangle_on_line Y I.val (f U) I.property.2 hfUY hfUI
  have hL'e : L'=L := c.line_unique Y.property I.val.property hL hL'
    I.property.2.2.1 hYL hYL' hIL hIL'
  have hfUL : (f U).val≤L := hL'e ▸ hfUL'
  let C := c.collinearity.commonNeighbors ⟨c.W,c.point_mem⟩ U
  let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1<Nat.card (c.collinearity.commonNeighbors ⟨c.W,c.point_mem⟩ U)
    rw [c.distance_two_common_neighbors_card hU]
    decide)
  obtain ⟨J,hJI⟩ := exists_ne (⟨I.val,hI⟩:C)
  have hneIJ : I.val≠J.val := fun he=>hJI (Subtype.ext he.symm)
  have hnot : ¬c.collinearity.Adj I.val J.val := c.common_neighbors_not_adj U I.val J.val hU hI J.property hneIJ
  have hfJ : f J.val=J.val := hperp J.val J.property.1
  have hfJU : c.collinearity.Adj J.val (f U) := hfJ ▸
    f.map_rel_iff.mpr (c.collinearity.adj_symm J.property.2)
  exact (c.common_neighbors_on_line_unique I.val J.val U (f U) hnot hneIJ
    ⟨hIU,c.collinearity.adj_symm J.property.2⟩ ⟨hfUI,hfJU⟩ ⟨hL,hIL⟩ hUL hfUL).symm

theorem graph_aut_eq_of_fixed_opposite (f : c.collinearity ≃g c.collinearity)
    (hbase : f ⟨c.W,c.point_mem⟩=⟨c.W,c.point_mem⟩)
    (hperp : ∀U:c.points,c.collinearity.Adj ⟨c.W,c.point_mem⟩ U→f U=U)
    {Y : Subgroup G} (hYL : Y≤c.oppositeFactor) (hY : Nat.card Y=3) (hne : Y≠c.W)
    (hK : c.K≤normalizer (Y:Set G))
    (hfY : f ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩=⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩) :
    f=SimpleGraph.Iso.refl := by
  let O (d:G) : c.points := ⟨Y.conjBy d,c.point_conjugate_mem (c.cubic_in_oppositeFactor_is_point hYL hY) d⟩
  have ho1 : O 1=⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ := Subtype.ext (conjBy_one Y)
  have hdist (d:G) (hd:d∈c.D) : c.collinearity.edist ⟨c.W,c.point_mem⟩ (O d)=2 :=
    c.opposite_cubic_conjugate_distance_two hYL hY hne d hd
  have hp (d:G) (hd:d∈c.oppositeConnection Y) :
      ∀e∈c.D,f (O e)=O e ↔ f (O (e*d))=O (e*d) := by
    rw [c.oppositeConnection_eq_closure] at hd
    induction hd using Subgroup.closure_induction with
    | mem d hd =>
      intro e he
      have ha : c.collinearity.Adj (O e) (O (e*d)) := by
        have hh := c.neighbor_conjugate hd.2 e
        rwa [←conjBy_mul] at hh
      exact ⟨fun hh=>c.fixes_opposite_neighbors f hperp (O e) (hdist e he) hh _ ha,
        fun hh=>c.fixes_opposite_neighbors f hperp (O (e*d)) (hdist _ (c.D.mul_mem he hd.1)) hh _
          (c.collinearity.adj_symm ha)⟩
    | one => intro e he; simp only [mul_one,iff_self]
    | mul a b ha hb iha ihb =>
      intro e he
      simpa only [mul_assoc] using (iha e he).trans (ihb (e*a) (c.D.mul_mem he (c.oppositeConnection_le_odd Y (by rwa [c.oppositeConnection_eq_closure]))))
    | inv a ha iha =>
      intro e he
      simpa only [inv_mul_cancel_right] using
        (iha (e*a⁻¹) (c.D.mul_mem he (c.D.inv_mem (c.oppositeConnection_le_odd Y (by rwa [c.oppositeConnection_eq_closure]))))).symm
  have hfix (d:G) (hd:d∈c.D) : f (O d)=O d := by
    have hi := hp d ((c.oppositeConnection_eq_odd hYL hY hne hK).symm ▸ hd) 1 c.D.one_mem
    simpa only [one_mul] using hi.mp (ho1.symm ▸ hfY)
  apply RelIso.ext
  intro U
  rcases (c.reachable_iff_withinTwo U).mp (c.original_point_reachable U) with he|ha|hd
  · exact he ▸ hbase
  · exact hperp U ha
  · obtain ⟨d,hdD,he⟩ := c.distance_two_mem_oddPointOrbit hYL hY hne hK hd
    have he' : U=O d := Subtype.ext he
    exact he'.symm ▸ hfix d hdD
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

