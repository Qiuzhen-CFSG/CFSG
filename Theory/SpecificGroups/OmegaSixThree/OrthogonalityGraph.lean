module

public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.FiniteGeometry

/-!
# The projective orthogonality graph in dimension six over the ternary field

The vertices are sign classes of vectors of norm `-1` for the diagonal form
`(1,1,1,1,1,-1)`, and adjacency is vanishing of its polar form. Every pair has
a walk of length two. For distinct nonadjacent points, two adjacent common
neighbors cover the induced common-neighbor graph, proving its connectedness.
Every edge and every third point have a common neighbor, giving the local
configuration used to fill pentagons by triangles.

The proof transfers exhaustive, kernel-checked coordinate certificates to the
actual quotient graph. `adj_point_iff`, `adj_point_polar_iff`, and
`point_eq_iff_smul` connect the graph to arbitrary vector representatives;
`coordinate_triangle` supplies a concrete orthogonal triangle.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §F.5,
Lemma F.5.8(2), printed pp. 303–304 (PDF pp. 314–315).
-/

@[expose] public section

open SixTernaryCoordinates
namespace OmegaSixThree.OrthogonalityGraph

/-- The projective point with the given finite coordinate index. -/
def coordinatePoint (i : Fin 117) : Point := point (Certificate.coords i) (Certificate.coords_norm i)

theorem coordinatePoint_surjective : Function.Surjective coordinatePoint := by
  intro x
  induction x using Quotient.inductionOn with | h v =>
    obtain ⟨i, hi⟩ := Certificate.coords_complete v.val v.property
    exact ⟨i, (point_eq_iff _ _ _ _).mpr hi⟩

instance : Finite Point := Finite.of_surjective coordinatePoint coordinatePoint_surjective
noncomputable instance : Fintype Point := Fintype.ofFinite Point
instance : Nonempty Point := ⟨coordinatePoint 0⟩

theorem adj_coordinatePoint_iff (i j : Fin 117) :
    graph.Adj (coordinatePoint i) (coordinatePoint j) ↔
      (Certificate.rows i).getLsbD j = true := (Certificate.rows_correct i j).symm

/-- Any two vertices have a common neighbor, including coincident or adjacent vertices. -/
theorem exists_common_neighbor (x y : Point) :
    ∃ z, graph.Adj x z ∧ graph.Adj y z := by
  obtain ⟨i, rfl⟩ := coordinatePoint_surjective x
  obtain ⟨j, rfl⟩ := coordinatePoint_surjective y
  obtain ⟨k, hik, hjk⟩ := Certificate.common_neighbor i j
  exact ⟨coordinatePoint k, (adj_coordinatePoint_iff i k).mpr hik,
    (adj_coordinatePoint_iff j k).mpr hjk⟩

/-- A concrete walk of length two joins any two projective points. -/
theorem exists_walk_length_two (x y : Point) : ∃ p : graph.Walk x y, p.length = 2 := by
  obtain ⟨z, hxz, hyz⟩ := exists_common_neighbor x y
  exact ⟨.cons hxz (.cons hyz.symm .nil), rfl⟩

theorem connected : graph.Connected := by
  refine { preconnected := ?_ }
  intro x y
  obtain ⟨p, _⟩ := exists_walk_length_two x y
  exact ⟨p⟩

theorem dist_le_two (x y : Point) : graph.dist x y ≤ 2 := by
  obtain ⟨p, hp⟩ := exists_walk_length_two x y
  simpa only [hp] using SimpleGraph.dist_le p

theorem edist_le_two (x y : Point) : graph.edist x y ≤ 2 := by
  obtain ⟨p, hp⟩ := exists_walk_length_two x y
  simpa [hp] using p.edist_le

/-- The common-neighbor graph of a distinct nonadjacent pair has two adjacent
vertices whose neighborhoods cover it. In particular it is connected. -/
theorem common_neighbor_centers (x y : Point) (hne : x ≠ y) (hn : ¬ graph.Adj x y) :
    ∃ r s, (graph.Adj x r ∧ graph.Adj y r) ∧
      (graph.Adj x s ∧ graph.Adj y s) ∧ graph.Adj r s ∧
      ∀ z, graph.Adj x z → graph.Adj y z → graph.Adj r z ∨ graph.Adj s z := by
  obtain ⟨i, rfl⟩ := coordinatePoint_surjective x
  obtain ⟨j, rfl⟩ := coordinatePoint_surjective y
  have hij : i ≠ j := fun h => hne (congrArg coordinatePoint h)
  have hn' : (Certificate.rows i).getLsbD j = false := by
    simpa only [adj_coordinatePoint_iff, Bool.not_eq_true] using hn
  obtain ⟨r, s, hr, hs, hrs, hc⟩ := Certificate.common_neighbor_centers i j hij hn'
  refine ⟨coordinatePoint r, coordinatePoint s, ?_, ?_, ?_, ?_⟩
  · exact ⟨(adj_coordinatePoint_iff _ _).mpr hr.1, (adj_coordinatePoint_iff _ _).mpr hr.2⟩
  · exact ⟨(adj_coordinatePoint_iff _ _).mpr hs.1, (adj_coordinatePoint_iff _ _).mpr hs.2⟩
  · exact (adj_coordinatePoint_iff _ _).mpr hrs
  · intro z hiz hjz
    obtain ⟨k, rfl⟩ := coordinatePoint_surjective z
    simpa only [adj_coordinatePoint_iff] using
      hc k ((adj_coordinatePoint_iff _ _).mp hiz) ((adj_coordinatePoint_iff _ _).mp hjz)

/-- The induced graph on the common neighbors of distinct nonadjacent points
is connected, as required for filling quadrilaterals by triangles. -/
theorem commonNeighbors_connected (x y : Point) (hne : x ≠ y) (hn : ¬ graph.Adj x y) :
    (graph.induce (graph.commonNeighbors x y)).Connected := by
  obtain ⟨r, s, hr, hs, hrs, hc⟩ := common_neighbor_centers x y hne hn
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨r, hr⟩, ?_⟩
  intro z
  rcases hc z.val z.property.1 z.property.2 with h | h
  · exact ⟨.cons h .nil⟩
  · exact ⟨.cons (v := (⟨s, hs⟩ : graph.commonNeighbors x y)) hrs (.cons h .nil)⟩

/-- Every edge and every third vertex have a common neighbor. -/
theorem edge_common_neighbor (x w v : Point) (hxw : graph.Adj x w) :
    ∃ a, graph.Adj x a ∧ graph.Adj w a ∧ graph.Adj v a := by
  obtain ⟨i, rfl⟩ := coordinatePoint_surjective x
  obtain ⟨j, rfl⟩ := coordinatePoint_surjective w
  obtain ⟨k, rfl⟩ := coordinatePoint_surjective v
  obtain ⟨r, hr⟩ := Certificate.edge_common_neighbor i j k ((adj_coordinatePoint_iff _ _).mp hxw)
  exact ⟨coordinatePoint r, (adj_coordinatePoint_iff _ _).mpr hr.1,
    (adj_coordinatePoint_iff _ _).mpr hr.2.1, (adj_coordinatePoint_iff _ _).mpr hr.2.2⟩

/-- The local configuration used to fill pentagons in F.5.8(2). -/
theorem pentagon_common_neighbor (x w v : Point) (hxw : graph.Adj x w)
    (_hvx : v ≠ x) (_hvw : v ≠ w) (_hnvx : ¬ graph.Adj v x) (_hnvw : ¬ graph.Adj v w) :
    ∃ a, graph.Adj x a ∧ graph.Adj w a ∧ graph.Adj v a := edge_common_neighbor x w v hxw

/-- The sixth coordinate line, the base point of the source geometry. -/
def axisPoint : Point := point ![0,0,0,0,0,1] (by decide)
/-- The line on the sum of the first two coordinate vectors. -/
def pair01Point : Point := point ![1,1,0,0,0,0] (by decide)
/-- The line on the sum of the third and fourth coordinate vectors. -/
def pair23Point : Point := point ![0,0,1,1,0,0] (by decide)

theorem coordinate_triangle : graph.Adj axisPoint pair01Point ∧
    graph.Adj pair01Point pair23Point ∧ graph.Adj pair23Point axisPoint := by
  change pairing ![0,0,0,0,0,1] ![1,1,0,0,0,0] = 0 ∧
    pairing ![1,1,0,0,0,0] ![0,0,1,1,0,0] = 0 ∧
    pairing ![0,0,1,1,0,0] ![0,0,0,0,0,1] = 0
  decide +kernel

/-- Negating a representative does not change the projective point. -/
theorem point_neg (v : Space) (hv : quadratic v = -1) :
    point (-v) (by simpa only [quadratic_neg] using hv) = point v hv :=
  (point_eq_iff _ _ _ _).mpr (Or.inr rfl)

/-- Orthogonality is invariant under independent nonzero changes of scale. -/
theorem pairing_smul_eq_zero_iff (c d : ZMod 3) (hc : c ≠ 0) (hd : d ≠ 0)
    (v w : Space) : pairing (c • v) (d • w) = 0 ↔ pairing v w = 0 := by
  rcases nonzero_scalar c hc with rfl | rfl <;>
    rcases nonzero_scalar d hd with rfl | rfl <;>
    simp [pairing_neg_left, pairing_neg_right]

theorem coordinate_triangle_distinct : axisPoint ≠ pair01Point ∧
    pair01Point ≠ pair23Point ∧ pair23Point ≠ axisPoint :=
  ⟨coordinate_triangle.1.ne, coordinate_triangle.2.1.ne, coordinate_triangle.2.2.ne⟩

theorem axisPoint_eq_coordinatePoint_zero : axisPoint = coordinatePoint 0 := by
  apply (point_eq_iff _ _ _ _).mpr
  left
  funext i
  fin_cases i <;> decide +kernel

end OmegaSixThree.OrthogonalityGraph
