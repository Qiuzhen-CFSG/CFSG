module

public import Stellmacher.PushingUp.DistanceTwoShift

/-!
# A chosen five-vertex configuration at critical distance four

Three successive distance-two shifts provide the five vertices in Stellmacher,
*Pushing up* (1986), (3.3), with generation at the right midpoint as well as the
two explicit shift generations. Reindexing around the second shift retains
the original theorem hypotheses. The preceding shift supplies the right-middle
generation because its far endpoint center lies in the other length-two edge
core by strict-distance kernel containment.

The source subgroups `F`, `Y`, `U`, and `D` are their literal ambient joins,
commutator, and core intersection. `Ubar` is the image of the internal subgroup
`U` in `G_a/Z(G_a)`, equivalently `U Z(G_a)/Z(G_a)` once `U ≤ G_a` is proved.
The public configuration records only proved graph data needed by the two
center decompositions; it assumes no finite vertex-set or finite free amalgam.

Source: B. Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (2.3) and the
configuration preceding (3.3)(1)--(3), journal pp.12 and 15.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

namespace DistanceFour

/-- The source (3.3) frame, chosen with an explicit right-middle generation. -/
public structure Configuration (S : Subgroup M) (a a' c u v : Vertex S) : Prop where
  critical : IsCriticalPair S a a'
  first_frame : DistanceTwoShift.Frame S a a' c
  first_shift : DistanceTwoShift.Conclusion S a a' c u
  second_frame : DistanceTwoShift.Frame S u c a
  second_shift : DistanceTwoShift.Conclusion S u c a v
  right_generation :
    edgeTwoCore S a c ⊔ edgeTwoCore S a' c = stabilizer S c

public noncomputable abbrev F (S : Subgroup M) (a' v : Vertex S) :=
  vertexZ S v ⊔ vertexZ S a'

public noncomputable abbrev Y (S : Subgroup M) (u c : Vertex S) :=
  ⁅vertexZ S u, vertexZ S c⁆

public noncomputable abbrev U (S : Subgroup M) (a c u : Vertex S) :=
  vertexZ S a ⊔ vertexZ S c ⊔ vertexZ S u

public noncomputable abbrev D (S : Subgroup M) (a a' c u v : Vertex S) :=
  vertexTwoCore S v ⊓ vertexTwoCore S u ⊓ vertexTwoCore S a ⊓
    vertexTwoCore S c ⊓ vertexTwoCore S a'

/-- The source barred subgroup, represented by its image in `G_a/Z(G_a)`. -/
public noncomputable abbrev Ubar (S : Subgroup M) (a c u : Vertex S) :=
  ((U S a c u).subgroupOf (stabilizer S a)).map
    (QuotientGroup.mk' (Subgroup.center (stabilizer S a)))

end DistanceFour

private theorem common_neighbor_for_omega
    (S : Subgroup M) {x y : Vertex S}
    (hxy : (cosetGraph S).dist x y = 2) :
    ∃ d : Vertex S, Adjacent S x d ∧ Adjacent S d y := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist x y
  have hpnon : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hp, hxy]
    omega
  refine ⟨p.penultimate, ?_, ?_⟩
  · have hdist : (cosetGraph S).dist x p.penultimate = 1 := by
      have hdrop := SimpleGraph.length_eq_dist_of_subwalk hp
        ((SimpleGraph.Walk.isSubwalk_rfl p).dropLast)
      rw [SimpleGraph.Walk.length_dropLast, hp, hxy] at hdrop
      omega
    exact (cosetGraph_adj S x p.penultimate).1
      (SimpleGraph.dist_eq_one_iff_adj.mp hdist)
  · exact (cosetGraph_adj S p.penultimate y).1 (p.adj_penultimate hpnon)

private theorem exists_midpoint_of_dist_four
    (S : Subgroup M) (a a' : Vertex S)
    (hdist : (cosetGraph S).dist a a' = 4) :
    ∃ c : Vertex S,
      (cosetGraph S).dist a c = 2 ∧
      (cosetGraph S).dist c a' = 2 := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist a a'
  let c := p.getVert 2
  have hlen : p.length = 4 := hp.trans hdist
  have hac : (cosetGraph S).dist a c = 2 := by
    have htake := SimpleGraph.length_eq_dist_of_subwalk hp
      (SimpleGraph.Walk.isSubwalk_take p 2)
    change (p.take 2).length = (cosetGraph S).dist a c at htake
    rw [SimpleGraph.Walk.take_length, hlen] at htake
    omega
  have hca' : (cosetGraph S).dist c a' = 2 := by
    have hdrop := SimpleGraph.length_eq_dist_of_subwalk hp
      (SimpleGraph.Walk.isSubwalk_drop p 2)
    change (p.drop 2).length = (cosetGraph S).dist c a' at hdrop
    rw [SimpleGraph.Walk.drop_length, hlen] at hdrop
    omega
  exact ⟨c, hac, hca'⟩

private theorem kernel_le_distanceTwo_edge [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (x y : Vertex S) (hx : InMVertexOrbit S x) (hy : InMVertexOrbit S y)
    (hxy : (cosetGraph S).dist x y = 2) :
    neighborhoodKernel S x ≤ edgeTwoCore S y x := by
  obtain ⟨d, hxd, hdy⟩ := common_neighbor_for_omega S hxy
  have hne : x ≠ y := by
    intro h
    subst y
    simp at hxy
  rw [edgeTwoCore_distanceTwo S T hTS x d y hx hy hxd hdy hne,
    incident_edgeTwoCore_eq_edgeStabilizer S T hTS x d hx hxd]
  exact fun _ hg => ⟨hg.1, hg.2 d hxd⟩

private theorem edgeTwoCore_le_right_stabilizer
    (S : Subgroup M) (x y : Vertex S) :
    edgeTwoCore S x y ≤ stabilizer S y :=
  (Subgroup.map_subtype_le (pCore 2 ↥(stabilizer S x ⊓ stabilizer S y))).trans
    inf_le_right

public theorem distanceFour_configuration_exists [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (hb4 : criticalDistance S = 4) :
    ∃ a a' c u v : Vertex S, DistanceFour.Configuration S a a' c u v := by
  have hb : 0 < criticalDistance S := by omega
  let x := mVertex S 1
  have hx : InMVertexOrbit S x := ⟨1, by simp [x]⟩
  obtain ⟨x', hcrit⟩ := criticalPair_exists S T hTS hP hSne x hx
  have hxx' : (cosetGraph S).dist x x' = 4 := hcrit.2.1.trans hb4
  obtain ⟨c0, hxc0, hc0x'⟩ := exists_midpoint_of_dist_four S x x' hxx'
  have hfirst : DistanceTwoShift.Frame S x x' c0 := ⟨by omega, hc0x'⟩
  obtain ⟨u0, hu0⟩ := criticalPair_distanceTwoShift S T hTS hP hSne hA
    x x' hcrit hb c0 hfirst
  have hu0x : (cosetGraph S).dist u0 x = 2 := by
    rw [SimpleGraph.dist_comm]
    exact hu0.distance_two
  have hsecond : DistanceTwoShift.Frame S u0 c0 x := ⟨by omega, hxc0⟩
  obtain ⟨v0, hv0⟩ := criticalPair_distanceTwoShift S T hTS hP hSne hA
    u0 c0 hu0.shifted_critical hb x hsecond
  have hv0u0 : (cosetGraph S).dist v0 u0 = 2 := by
    rw [SimpleGraph.dist_comm]
    exact hv0.distance_two
  have hthird : DistanceTwoShift.Frame S v0 x u0 := ⟨by omega, hu0x⟩
  obtain ⟨w0, hw0⟩ := criticalPair_distanceTwoShift S T hTS hP hSne hA
    v0 x hv0.shifted_critical hb u0 hthird
  have hx' := (criticalPair_path T hTS hP hSne x x' hcrit hb).opposite_inMVertexOrbit
  have hc0 := (criticalPair_path T hTS hP hSne u0 c0 hu0.shifted_critical hb)
    |>.opposite_inMVertexOrbit
  have hZx'K : vertexZ S x' ≤ neighborhoodKernel S c0 :=
    vertexZ_le_neighborhoodKernel_of_dist_lt S hx' (by
      rw [SimpleGraph.dist_comm]
      omega)
  have hKedge : neighborhoodKernel S c0 ≤ edgeTwoCore S x c0 :=
    kernel_le_distanceTwo_edge S T hTS c0 x hc0 hx (by
      rw [SimpleGraph.dist_comm]
      exact hxc0)
  have hZx'E : vertexZ S x' ≤ edgeTwoCore S c0 x := by
    change vertexZ S x' ≤ twoCoreAmbient (stabilizer S c0 ⊓ stabilizer S x)
    rw [inf_comm]
    exact hZx'K.trans hKedge
  refine ⟨u0, c0, x, v0, w0, hu0.shifted_critical,
    hsecond, hv0, hthird, hw0, ?_⟩
  apply le_antisymm (sup_le
    (edgeTwoCore_le_right_stabilizer S u0 x)
    (edgeTwoCore_le_right_stabilizer S c0 x))
  rw [← hu0.generates_left_stabilizer]
  exact sup_le le_sup_left (hZx'E.trans le_sup_right)

end Stellmacher.PushingUp
