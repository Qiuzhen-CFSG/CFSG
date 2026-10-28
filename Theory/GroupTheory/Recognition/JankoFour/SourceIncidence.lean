module

public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Markers
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Cardinalities
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneChart
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LineAction
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PointChart
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneMaximal
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.CoreFaithful
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LineClosure
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneOrbits
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.EdgeFixer
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneNonneighbors
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneUniqueness
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.CoreIntersections
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Connectivity
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LinePermutations
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.CommonFixers
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.OrbitTransport
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Coplanarity
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LineOrbitals

/-!
# Incidence consequences of the marked AS91 local groups

The explicit earlier-section `LocalData` retains the same original cubic,
Todd and line-group markings. Its proved consequences include (6.1), the
string condition, the radical's fixation of incident objects, the five-point
line and 77-point plane counts, and the literal seven-plane action kernel.
The literal plane chart and flag transitivity are constructed from the cubic
overlap maps. The five-point action has kernel K and full symmetric image;
a lift from S supplies the source edge element and line transitivity.
The point chart uses the same Todd projection and derives the marked native
incidence from the original intersection. The plane-point stabilizer is maximal,
and the radical acts transitively and regularly, allowing the kernel, on the
other four points of each line. Its action on all neighbors is faithful.
Neighboring radicals meet in the line three-space, using the supplied natural
module marking. This gives unique lines, plane closure and the literal plane-edge
orbit; the radical point stabilizer has index four and its intersection with R
has order 512.
The plane chart now identifies actual adjacency, gives the 1/60/16 rank-three
action and all three point–line orbits, and the original K supplies the edge
stabilizer element outside H. The original radical maps onto the native hexad
kernel, which acts regularly on the sixteen disjoint hexads. Hence E is
transitive on the plane's nonneighbors, its point stabilizer is E∩Q of order
128, and E supplements that stabilizer in M∩H. The ambient two-point
stabilizer normalizes this same kernel. Native sextet maximality and the
1771-element marker orbit identify its normalizer inside M with M∩H. Thus
the ambient two-point stabilizer lies in H, and the plane through the
nonadjacent pair is unique among all ambient planes. The nonadjacent point
radicals now meet precisely in the plane-marker subgroup. The original
marker-conjugate standing hypothesis then gives every clause of (6.2),
including the exact conjugate-map implication needed by source fusion.
All three ambient residues are connected by the actual overlap generation
and the left coset action; (6.5)(2) supplies the remaining premise for ambient
connectivity. The S factor realizes every line permutation while fixing all
incident planes, giving the collinear triangle-permutation branch. The zero
orbital is identified exactly, and radical intersections fix common neighbors.
All five native labels and their valencies transport through the same Todd
chart; their native orbit classification remains to be supplied.
The finite-simple consumer also obtains
faithfulness of the point action.

The conclusions below supply these fields of the unchanged
`SourceCycleBase.Input`. Construction of the remaining geometry,
fusion and ambient generation is still required; no existence of Input or ambient
recognition is asserted by this module.

The overlap-generated residues are connected, and global connectivity follows
from the retained source generation equation. The line action realizes every
permutation of its five points while fixing incident planes. The literal Todd
chart transports all five labels and their valencies; native common-octad
coplanarity proves the unchanged first-three-label coplanarity clause. Plane
markers also fix every common neighbor of a nonadjacent point pair; their
containment in its plane still requires the remaining native intersection step.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), §§5–6, pp.599–602.
-/

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open Subgroup SourceCycleBase
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The established Input clauses, on precisely the supplied point and line data.
The simplicity instance is inherited from the original recognition consumer. -/
theorem source_incidence_consequences [IsSimpleGroup G] (h : IsTypeJ4 z) (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    (∀ l : Line a.L, {x | OnLine a.L x l}.ncard = 5) ∧
    (∀ π : Plane z, {x | OnPlane a.P x π}.ncard = 77) ∧
    (∀ x l π, OnLine a.L x l → LineOnPlane a.L l π → OnPlane a.P x π) ∧
    (∀ x (u : coreAt a.P x) l, OnLine a.L x l → (u : G) • l = l) ∧
    (∀ x (u : coreAt a.P x) π, OnPlane a.P x π → (u : G) • π = π) ∧
    (∀ π x, marker π ∈ coreAt a.P x ↔ OnPlane a.P x π) :=
  ⟨a.point_corefree, a.line_card, a.plane_card, a.string,
    a.core_fixes_lines, a.core_fixes_planes, a.marker_mem_core⟩


/-- Further unchanged Input fields, with the supplied point and line groups.
The actual edge element, plane chart and flag representatives are constructed;
no geometric conclusion is assumed in `LocalData`. -/
theorem source_incidence_flags [IsSimpleGroup G] (h : IsTypeJ4 z) (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    Nonempty (PlaneChart a.P a.L) ∧
    (∀ x l π, OnLine a.L x l → OnPlane a.P x π → LineOnPlane a.L l π →
      ∃ g : G, GraphUniquenessSystem.Cosets.vertex a.P.M g = x ∧
        GraphUniquenessSystem.Cosets.vertex a.L.G₂ g = l ∧
        GraphUniquenessSystem.Cosets.vertex (centralizer z) g = π) ∧
    (∃ t : G, t ∈ centralizer z ∧ t ∈ a.L.G₂ ∧ t ∉ a.P.M ∧ t*t ∈ a.P.M ∧
      GraphUniquenessSystem.Cosets.LineTransitive a.P.M t a.L.G₂) ∧
    (∀ g : a.L.G₂,
      (∀ x : Point a.P, OnLine a.L x (GraphUniquenessSystem.Cosets.vertex a.L.G₂ 1) →
        (g : G) • x = x) ↔ (g : G) ∈ a.d.K) :=
  ⟨a.point_corefree,⟨a.planeChart⟩,fun x l π hxl _ hlπ => a.flag_transitive x l π hxl hlπ,
    a.exists_edge_element,a.point_action_kernel⟩


/-- The point chart and radical action fields, with the original quotient maps.
Ambient simplicity is retained explicitly for the actual recognition consumer. -/
theorem source_incidence_residue_actions [IsSimpleGroup G] (h : IsTypeJ4 z) (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    Nonempty (ResidueChart a.P a.L) ∧
    IsCoatom (a.P.M.subgroupOf (centralizer z)) ∧
    (∀ x l, OnLine a.L x l → ∀ y b,
      OnLine a.L y l → y ≠ x → OnLine a.L b l → b ≠ x →
        ∃ u : coreAt a.P x, (u : G) • y = b) ∧
    (∀ x l, OnLine a.L x l → ∀ (u : coreAt a.P x) y,
      OnLine a.L y l → y ≠ x → (u : G) • y = y →
        ∀ b, OnLine a.L b l → (u : G) • b = b) ∧
    (∀ x (u : coreAt a.P x), (∀ y, Adj a.L x y → (u : G) • y = y) → (u : G) = 1) :=
  ⟨a.point_corefree,⟨a.residueChart⟩,a.plane_maximal,
    a.core_transitive_other,a.core_regular_other,a.core_faithful_neighbors⟩


/-- The natural-module intersection argument supplies three further unchanged
Input clauses, retaining the original radicals, three-space and edge element. -/
theorem source_incidence_line_closure [IsSimpleGroup G] (h : IsTypeJ4 z) (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    (∀ y : Point a.P, OnLine a.L y (GraphUniquenessSystem.Cosets.vertex a.L.G₂ 1) →
      y ≠ GraphUniquenessSystem.Cosets.vertex a.P.M 1 →
      a.P.E ⊓ coreAt a.P y = a.d.space ∧
        ((MulAction.stabilizer G y).subgroupOf a.P.E).index = 4) ∧
    Nat.card (a.d.R.subgroupOf a.P.E) = 512 ∧
    (∀ x y, Adj a.L x y → ∃! l, OnLine a.L x l ∧ OnLine a.L y l) ∧
    (∀ x y l π, x ≠ y → OnLine a.L x l → OnLine a.L y l →
      OnPlane a.P x π → OnPlane a.P y π → LineOnPlane a.L l π) ∧
    (∃ t : G, t ∈ centralizer z ∧ t ∈ a.L.G₂ ∧ t ∉ a.P.M ∧ t*t ∈ a.P.M ∧
      GraphUniquenessSystem.Cosets.LineTransitive a.P.M t a.L.G₂ ∧
      ∀ x y, (∃ k : centralizer z,
        ((k : G) • GraphUniquenessSystem.Cosets.vertex a.P.M 1 = x ∧
          (k : G) • GraphUniquenessSystem.Cosets.vertex a.P.M t = y) ∨
        ((k : G) • GraphUniquenessSystem.Cosets.vertex a.P.M 1 = y ∧
          (k : G) • GraphUniquenessSystem.Cosets.vertex a.P.M t = x)) ↔
        Adj a.L x y ∧ OnPlane a.P x (GraphUniquenessSystem.Cosets.vertex (centralizer z) 1) ∧
          OnPlane a.P y (GraphUniquenessSystem.Cosets.vertex (centralizer z) 1)) := by
  refine ⟨a.point_corefree,?_,a.radical_R_card,a.unique_line,a.plane_closed,?_⟩
  · intro y hy hyx
    exact ⟨a.core_intersection_base y hy hyx,a.radical_point_stabilizer_index y hy hyx⟩
  · obtain ⟨t,htH,htN,htM,htsq,httrans⟩ := a.exists_edge_element
    exact ⟨t,htH,htN,htM,htsq,httrans,a.local_edge t htH htN htM⟩

/-- The actual rank-three plane geometry, all three point–line orbits, and
edge-fixer clause for the supplied local groups. Ambient simplicity is retained
from the finite-simple recognition consumer; global plane uniqueness and
ambient generation are separate remaining source obligations. -/
theorem source_incidence_plane_orbits [IsSimpleGroup G] (h : IsTypeJ4 z) (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    (∀ π x, OnPlane a.P x π → {y | OnPlane a.P y π ∧ Adj a.L x y}.ncard = 60) ∧
    (∀ π x, OnPlane a.P x π → {y | OnPlane a.P y π ∧ y ≠ x ∧ ¬ Adj a.L x y}.ncard = 16) ∧
    (∀ π x u v, OnPlane a.P x π → OnPlane a.P u π → OnPlane a.P v π →
      ((u = x ↔ v = x) ∧ (Adj a.L x u ↔ Adj a.L x v)) →
      ∃ g : G, g • π = π ∧ g • x = x ∧ g • u = v) ∧
    (∀ π x l, OnPlane a.P x π → LineOnPlane a.L l π →
      ∃ i : Fin 3, PlanePairType a.L i x l) ∧
    (∀ π x y l m (i : Fin 3), OnPlane a.P x π → OnPlane a.P y π →
      LineOnPlane a.L l π → LineOnPlane a.L m π →
      PlanePairType a.L i x l → PlanePairType a.L i y m →
      ∃ g : G, g • π = π ∧ g • x = y ∧ g • l = m) ∧
    (∀ π x, OnPlane a.P x π → ∀ i : Fin 3,
      ∃ l, LineOnPlane a.L l π ∧ PlanePairType a.L i x l) ∧
    (∀ t : G, t ∈ a.L.G₂ →
      ¬ a.P.M ⊓ a.P.M.comap (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer z) :=
  ⟨a.point_corefree,a.plane_neighbor_card,a.plane_nonneighbor_card,a.plane_rank_three,
    a.plane_pair_types,a.plane_pair_orbits,a.plane_pair_types_realized,a.edge_fixer⟩

/-- The radical part of (5.3)(2), using the same cubic quotient and the
actual disjoint-hexad action. This does not assert ambient plane uniqueness. -/
theorem source_incidence_nonneighbor_radical [IsSimpleGroup G] (h : IsTypeJ4 z)
    (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    a.radicalDesign.range = (Sporadic.Mathieu.m22HexadPointwiseKernel a.P.hexad).map
      Sporadic.Mathieu.M22ValueBound.Concrete.inclusion ∧
    a.radicalDesign.ker = (ambientCore z).subgroupOf a.P.E ∧
    Nat.card (a.P.E ⊓ ambientCore z : Subgroup G) = 128 ∧
    ∀ u : Point a.P, OnPlane a.P u (GraphUniquenessSystem.Cosets.vertex (centralizer z) 1) →
      u ≠ GraphUniquenessSystem.Cosets.vertex a.P.M 1 →
      ¬ Adj a.L (GraphUniquenessSystem.Cosets.vertex a.P.M 1) u →
      (∀ v : Point a.P, OnPlane a.P v (GraphUniquenessSystem.Cosets.vertex (centralizer z) 1) →
        v ≠ GraphUniquenessSystem.Cosets.vertex a.P.M 1 →
        ¬ Adj a.L (GraphUniquenessSystem.Cosets.vertex a.P.M 1) v →
        ∃ e : a.P.E, (e : G) • u = v) ∧
      (MulAction.stabilizer G u).subgroupOf a.P.E = (ambientCore z).subgroupOf a.P.E ∧
      Nat.card ((MulAction.stabilizer G u).subgroupOf a.P.E) = 128 ∧
      (∀ m ∈ a.P.M ⊓ centralizer z,
        ∃ e : a.P.E, ∃ k ∈ a.P.M ⊓ centralizer z ⊓ MulAction.stabilizer G u,
          m = (e : G)*k) ∧
      a.P.M ⊓ MulAction.stabilizer G u ≤
        normalizer ((a.P.E ⊓ ambientCore z : Subgroup G) : Set G) := by
  refine ⟨a.point_corefree,a.radicalDesign_range_eq,a.radicalDesign_ker,a.radical_core_card,?_⟩
  intro u hu hne hn
  exact ⟨fun v hv hve hvn => a.radical_nonneighbor_transitive u v hu hv hne hve hn hvn,
    a.radical_nonneighbor_stabilizer u hu hne hn,
    a.radical_nonneighbor_stabilizer_card u hu hne hn,
    a.nonneighbor_overlap_supplement u hu hne hn,
    a.nonneighbor_stabilizer_normalizes_kernel u hu hne hn⟩

/-- The point-side maximality and ambient unique-plane clauses of unchanged
Input, with the literal kernel normalizer and two-point stabilizer. -/
theorem source_incidence_plane_uniqueness [IsSimpleGroup G] (h : IsTypeJ4 z)
    (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    IsCoatom ((centralizer z).subgroupOf a.P.M) ∧
    a.P.M ⊓ normalizer ((a.P.E ⊓ ambientCore z : Subgroup G) : Set G) =
      a.P.M ⊓ centralizer z ∧
    (∀ u : Point a.P, OnPlane a.P u (GraphUniquenessSystem.Cosets.vertex (centralizer z) 1) →
      u ≠ GraphUniquenessSystem.Cosets.vertex a.P.M 1 →
      ¬ Adj a.L (GraphUniquenessSystem.Cosets.vertex a.P.M 1) u →
      a.P.M ⊓ MulAction.stabilizer G u ≤ centralizer z) ∧
    (∀ π x y, OnPlane a.P x π → OnPlane a.P y π → x ≠ y →
      ¬ Adj a.L x y → ∀ σ, OnPlane a.P x σ → OnPlane a.P y σ → σ = π) :=
  ⟨a.point_corefree,a.vertex_maximal,a.radical_core_normalizer,
    a.nonneighbor_stabilizer_le_plane,a.unique_plane⟩

/-- The earlier intersection mathematics required by the independent fusion
constructor, including its exact standing hypothesis and conjugate-map convention. -/
theorem source_incidence_core_intersections [IsSimpleGroup G] (h : IsTypeJ4 z)
    (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    (∀ π x y, OnPlane a.P x π → OnPlane a.P y π → x ≠ y →
      ¬ Adj a.L x y → coreAt a.P x ⊓ coreAt a.P y = zpowers (marker π)) ∧
    (∀ x y, (∃ w ∈ coreAt a.P x ⊓ coreAt a.P y, IsConj z w) →
      x = y ∨ Adj a.L x y ∨ PlaneDistanceTwo a.L x y) ∧
    (∀ g : G, a.P.E.map (MulAut.conj g).toMonoidHom ≠ a.P.E →
      (∃ w ∈ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom, IsConj z w) →
      ∀ v ∈ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom, v ≠ 1 → IsConj z v) :=
  ⟨a.point_corefree,a.nonadjacent_core_intersection,a.intersection_point_alternatives,
    a.source_six_two_three_map⟩

/-- Residual connectivity from the literal local groups. The only premise of
ambient connectivity is exactly the independent (6.5)(2) generation equation. -/
theorem source_incidence_connectivity [IsSimpleGroup G] (h : IsTypeJ4 z)
    (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    (∀ u : Object a.L,
      ((incidenceGraph a.L).induce {v | IncidentObject a.L u v}).Connected) ∧
    (centralizer z ⊔ a.P.M = ⊤ → (incidenceGraph a.L).Connected) :=
  ⟨a.point_corefree,a.residues_connected,a.geometry_connected_of_generate⟩

/-- Exact zero orbital, the collinear triangle branch and the initial
common-neighbor calculation, on the supplied P,L and their original charts. -/
theorem source_incidence_line_permutations [IsSimpleGroup G] (h : IsTypeJ4 z)
    (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    (∀ x l k, LineType a.residueChart 0 x l k ↔ OnLine a.L x l ∧ k = l) ∧
    (∀ (l : Line a.L) (v : Fin 3 → Point a.P), Function.Injective v →
      (∀ i, OnLine a.L (v i) l) → ∀ σ : Equiv.Perm (Fin 3),
      ∃ g : G, g • l = l ∧ (∀ π, LineOnPlane a.L l π → g • π = π) ∧
        ∀ i : Fin 3, g • v i = v (σ i)) ∧
    (∀ x y π, DistanceTwo a.L x y → OnPlane a.P x π → OnPlane a.P y π →
      ∀ u, Adj a.L x u → Adj a.L y u → marker π • u = u) :=
  ⟨a.point_corefree,a.delta_zero,a.collinear_triple_permutations,
    a.marker_fixes_common_neighbor⟩

/-- Literal native labels and valencies at every point, ready for the
remaining native five-orbit calculation in (5.4). -/
theorem source_incidence_line_types [IsSimpleGroup G] (h : IsTypeJ4 z)
    (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    (∀ (i : Fin 5) (x : Point a.P)
      (l m : {l : Line a.L // OnLine a.L x l}),
      LineType a.residueChart i x l.val m.val ↔
        Native.Delta i (a.residueChart.linesAt x l) (a.residueChart.linesAt x m)) ∧
    (∀ (i : Fin 5) (x : Point a.P) (l : {l : Line a.L // OnLine a.L x l}),
      {m | LineType a.residueChart i x l.val m}.ncard =
        {m | Native.Delta i (a.residueChart.linesAt x l) m}.ncard) :=
  ⟨a.point_corefree,lineType_at a.residueChart,lineType_card a.residueChart⟩

/-- AS91 (5.4)(2) for the supplied point and line groups, with all three
coplanar labels read through the original Todd projection. -/
theorem source_incidence_coplanarity [IsSimpleGroup G] (h : IsTypeJ4 z)
    (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    (∀ x l m, OnLine a.L x l → OnLine a.L x m →
      (Coplanar a.L l m ↔ ∃ i : Fin 5, i.val ≤ 2 ∧ LineType a.residueChart i x l m)) :=
  ⟨a.point_corefree,a.delta_coplanar⟩

/-- AS91 (5.4)(1) and its five valencies for the original local groups.
The labels and stabilizer action use the unchanged Todd residue chart. -/
theorem source_incidence_orbitals [IsSimpleGroup G] (h : IsTypeJ4 z)
    (a : LocalData h) :
    a.P.M.normalCore = ⊥ ∧
    (∀ x l k, OnLine a.L x l → OnLine a.L x k →
      ∃! i : Fin 5, LineType a.residueChart i x l k) ∧
    (∀ x l k m (i : Fin 5),
      LineType a.residueChart i x l k → LineType a.residueChart i x l m →
      ∃ g : G, g • x = x ∧ g • l = l ∧ g • k = m) ∧
    (∀ x l, OnLine a.L x l → ∀ i : Fin 5,
      {k | LineType a.residueChart i x l k}.ncard =
        (![1,42,56,1008,2688] : Fin 5 → ℕ) i) ∧
    (∀ x l k (i : Fin 5), LineType a.residueChart i x l k →
      LineType a.residueChart i x k l ∧
      ∃ g : G, g • x = x ∧ g • l = k ∧ g • k = l) :=
  ⟨a.point_corefree,a.orbital_partition,a.orbital_transitive,a.delta_card,
    fun _ _ _ _ ht => ⟨a.lineType_symm ht,a.line_pair_swap ht⟩⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
