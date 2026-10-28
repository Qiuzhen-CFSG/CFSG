module

public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Cosets
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups.NativePlaneFlags

/-!
# Earlier-source input for the AS91 section 7 argument

`Input` is a single conditional interface; it asserts no existence theorem.
Its producer retains the construction of the point and line groups, the native
residue markings, AS91 (5.1)–(5.7), (6.1), (6.5), and the algebraic premises
of the actual uniqueness system. In particular neither a contraction property
nor any conclusion of section 7 is a field.

The charts are at the base point and plane. All other charts and orbital
labels are transported by the literal left action. The point chart uses the
same Todd projection for lines and planes. The plane chart uses the original
cubic projection and retains the chosen hexad and pair. The regularity field
concerns the four *other* points on a line and allows the action kernel.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), pp.599–603. The sections
2–3 native finite incidence theorems remain obligations of this module family,
not assumptions in this interface.
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase

open Subgroup GraphUniquenessSystem LocalGeometry LocalGeometry.LocalSubgroups
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The two incidence charts at M, equivariant for one and the same marked
projection M → M₂₄. Equality of parts is equality of native geometric objects. -/
structure ResidueChart (P : PointData z) (L : LineData z P) where
  lines : {l : Line L // OnLine L (Cosets.vertex P.M 1) l} ≃ Native.Line
  planes : {π : Plane z // OnPlane P (Cosets.vertex P.M 1) π} ≃ Native.Plane
  incidence : ∀ l π, LineOnPlane L l.val π.val ↔ Native.Incident (lines l) (planes π)
  lines_equivariant : ∀ (m : P.M) l l', (m : G) • l.val = l'.val →
    (lines l').parts = P.projection m • (lines l).parts
  planes_equivariant : ∀ (m : P.M) π π', (m : G) • π.val = π'.val →
    (planes π').parts = P.projection m • (planes π).parts

/-- Transport of the actual native line types; the witness g is the same
representative for both lines and the middle point. -/
def LineType {P : PointData z} {L : LineData z P} (c : ResidueChart P L)
    (i : Fin 5) (x : Point P) (l k : Line L) : Prop :=
  ∃ (g : G) (a b : {l : Line L // OnLine L (Cosets.vertex P.M 1) l}),
    Cosets.vertex P.M g = x ∧ g • a.val = l ∧ g • b.val = k ∧
      Native.Delta i (c.lines a) (c.lines b)

abbrev Hexad := {B : Finset (Fin 22) // B ∈ m22Blocks}
abbrev Pair := {A : Finset (Fin 22) // A.card = 2}

/-- The base-plane chart, retaining the actual cubic projection and both
specified overlap markings, rather than only their subgroup indices. -/
structure PlaneChart (P : PointData z) (L : LineData z P) where
  points : {x : Point P // OnPlane P x (Cosets.vertex (centralizer z) 1)} ≃ Hexad
  lines : {l : Line L // LineOnPlane L l (Cosets.vertex (centralizer z) 1)} ≃ Pair
  incidence : ∀ x l, OnLine L x.val l.val ↔ (lines l).val ⊆ (points x).val
  point_marking : (points ⟨Cosets.vertex P.M 1, ⟨1, rfl, rfl⟩⟩).val = P.hexad
  line_marking : (lines ⟨Cosets.vertex L.G₂ 1, ⟨1, rfl, rfl⟩⟩).val = L.pair
  points_equivariant : ∀ (h : centralizer z) (a : m22DesignAut),
    CubicLift.projection P.cubic h = m22DesignAutToAut a →
    ∀ x x', (h : G) • x.val = x'.val → (points x').val = a • (points x).val
  lines_equivariant : ∀ (h : centralizer z) (a : m22DesignAut),
    CubicLift.projection P.cubic h = m22DesignAutToAut a →
    ∀ l l', (h : G) • l.val = l'.val → (lines l').val = a • (lines l).val

/-- The three alternatives in (5.3.3), including their actual incidences. -/
def PlanePairType {P : PointData z} (L : LineData z P)
    (i : Fin 3) (x : Point P) (l : Line L) : Prop :=
  match i.val with
  | 0 => OnLine L x l
  | 1 => ∀ y, OnLine L y l → Adj L x y
  | _ => {y | OnLine L y l ∧ Adj L x y}.ncard = 3

abbrev Object {P : PointData z} (L : LineData z P) := Point P ⊕ (Line L ⊕ Plane z)

def IncidentObject {P : PointData z} (L : LineData z P) : Object L → Object L → Prop
  | .inl x, .inr (.inl l) => OnLine L x l
  | .inr (.inl l), .inl x => OnLine L x l
  | .inl x, .inr (.inr π) => OnPlane P x π
  | .inr (.inr π), .inl x => OnPlane P x π
  | .inr (.inl l), .inr (.inr π) => LineOnPlane L l π
  | .inr (.inr π), .inr (.inl l) => LineOnPlane L l π
  | _, _ => False

def incidenceGraph {P : PointData z} (L : LineData z P) : SimpleGraph (Object L) where
  Adj := IncidentObject L
  symm := ⟨by
    intro a b
    rcases a with a | a <;> rcases b with b | b
    · exact id
    · rcases b <;> exact id
    · rcases a <;> exact id
    · rcases a <;> rcases b <;> exact id⟩
  loopless := ⟨by
    intro a
    rcases a with a | a
    · exact id
    · rcases a <;> exact id⟩

/-- All earlier-source premises of the section 7 proof. Existence of this
record is retained by the source-recognition producer. -/
structure Input (_h : IsTypeJ4 z) where
  P : PointData z
  L : LineData z P
  t : G
  t_plane : t ∈ centralizer z
  t_line : t ∈ L.G₂
  t_not_point : t ∉ P.M
  t_sq : t * t ∈ P.M
  faithful : P.M.normalCore = ⊥
  generate : centralizer z ⊔ P.M = ⊤
  vertex_maximal : IsCoatom ((centralizer z).subgroupOf P.M)
  plane_maximal : IsCoatom (P.M.subgroupOf (centralizer z))
  edge_fixer : ¬ P.M ⊓ P.M.comap (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer z
  line_transitive : Cosets.LineTransitive P.M t L.G₂
  residue : ResidueChart P L
  plane : PlaneChart P L
  /-- The local edge orbit is exactly the edges within the original plane. -/
  local_edge : ∀ a b,
    (∃ h : centralizer z,
      ((h : G) • Cosets.vertex P.M 1 = a ∧ (h : G) • Cosets.vertex P.M t = b) ∨
      ((h : G) • Cosets.vertex P.M 1 = b ∧ (h : G) • Cosets.vertex P.M t = a)) ↔
    Adj L a b ∧ OnPlane P a (Cosets.vertex (centralizer z) 1) ∧
      OnPlane P b (Cosets.vertex (centralizer z) 1)
  line_card : ∀ l : Line L, {x | OnLine L x l}.ncard = 5
  flag_transitive : ∀ x l π, OnLine L x l → OnPlane P x π → LineOnPlane L l π →
    ∃ g : G, Cosets.vertex P.M g = x ∧ Cosets.vertex L.G₂ g = l ∧
      Cosets.vertex (centralizer z) g = π
  geometry_connected : (incidenceGraph L).Connected
  residues_connected : ∀ a : Object L,
    ((incidenceGraph L).induce {b | IncidentObject L a b}).Connected
  string : ∀ x l π, OnLine L x l → LineOnPlane L l π → OnPlane P x π
  unique_line : ∀ x y, Adj L x y → ∃! l, OnLine L x l ∧ OnLine L y l
  plane_closed : ∀ x y l π, x ≠ y → OnLine L x l → OnLine L y l →
    OnPlane P x π → OnPlane P y π → LineOnPlane L l π
  core_fixes_lines : ∀ x (e : coreAt P x) l, OnLine L x l → (e : G) • l = l
  core_fixes_planes : ∀ x (e : coreAt P x) π, OnPlane P x π → (e : G) • π = π
  core_transitive_other : ∀ x l, OnLine L x l → ∀ a b,
    OnLine L a l → a ≠ x → OnLine L b l → b ≠ x →
      ∃ e : coreAt P x, (e : G) • a = b
  core_regular_other : ∀ x l, OnLine L x l → ∀ (e : coreAt P x) a,
    OnLine L a l → a ≠ x → (e : G) • a = a →
      ∀ b, OnLine L b l → (e : G) • b = b
  core_faithful_neighbors : ∀ x (e : coreAt P x),
    (∀ y, Adj L x y → (e : G) • y = y) → (e : G) = 1
  plane_card : ∀ π : Plane z, {x | OnPlane P x π}.ncard = 77
  plane_neighbor_card : ∀ π x, OnPlane P x π →
    {y | OnPlane P y π ∧ Adj L x y}.ncard = 60
  plane_nonneighbor_card : ∀ π x, OnPlane P x π →
    {y | OnPlane P y π ∧ y ≠ x ∧ ¬ Adj L x y}.ncard = 16
  plane_rank_three : ∀ π x u v, OnPlane P x π → OnPlane P u π → OnPlane P v π →
    ((u = x ↔ v = x) ∧ (Adj L x u ↔ Adj L x v)) →
    ∃ g : G, g • π = π ∧ g • x = x ∧ g • u = v
  unique_plane : ∀ π x y, OnPlane P x π → OnPlane P y π → x ≠ y →
    ¬ Adj L x y → ∀ σ, OnPlane P x σ → OnPlane P y σ → σ = π
  plane_pair_types : ∀ π x l, OnPlane P x π → LineOnPlane L l π →
    ∃ i : Fin 3, PlanePairType L i x l
  plane_pair_orbits : ∀ π x y l m (i : Fin 3),
    OnPlane P x π → OnPlane P y π → LineOnPlane L l π → LineOnPlane L m π →
    PlanePairType L i x l → PlanePairType L i y m →
    ∃ g : G, g • π = π ∧ g • x = y ∧ g • l = m
  plane_pair_types_realized : ∀ π x, OnPlane P x π → ∀ i : Fin 3,
    ∃ l, LineOnPlane L l π ∧ PlanePairType L i x l
  orbital_partition : ∀ x l k, OnLine L x l → OnLine L x k →
    ∃! i : Fin 5, LineType residue i x l k
  orbital_transitive : ∀ x l k m (i : Fin 5),
    LineType residue i x l k → LineType residue i x l m →
    ∃ g : G, g • x = x ∧ g • l = l ∧ g • k = m
  delta_zero : ∀ x l k, LineType residue 0 x l k ↔ OnLine L x l ∧ k = l
  delta_coplanar : ∀ x l k, OnLine L x l → OnLine L x k →
    (Coplanar L l k ↔ ∃ i : Fin 5, i.val ≤ 2 ∧ LineType residue i x l k)
  delta_card : ∀ x l, OnLine L x l → ∀ i : Fin 5,
    {k | LineType residue i x l k}.ncard = (![1, 42, 56, 1008, 2688] : Fin 5 → ℕ) i
  delta_one_neighbors : ∀ x y l k, OnLine L x l → OnLine L y l → y ≠ x →
    LineType residue 1 x l k → {u | OnLine L u k ∧ Adj L y u}.ncard = 3
  delta_two_neighbors : ∀ x y l k, OnLine L x l → OnLine L y l → y ≠ x →
    LineType residue 2 x l k → ∀ u, OnLine L u k → Adj L y u
  core_stabilizer_transitive : ∀ x y l k (i : Fin 5), OnLine L x l →
    OnLine L y l → y ≠ x → 1 < i.val → LineType residue i x l k →
    ∀ a b, OnLine L a k → a ≠ x → OnLine L b k → b ≠ x →
    ∃ e : coreAt P x, (e : G) • y = y ∧ (e : G) • a = b
  triangles_in_plane : ∀ a b c, Adj L a b → Adj L b c → Adj L c a →
    ∃ π, OnPlane P a π ∧ OnPlane P b π ∧ OnPlane P c π
  triangle_permutations : ∀ a b c, Adj L a b → Adj L b c → Adj L c a →
    ∀ σ : Equiv.Perm (Fin 3), ∃ g : G,
      ∀ i : Fin 3, g • (![a,b,c] : Fin 3 → Point P) i = (![a,b,c] : Fin 3 → Point P) (σ i)
  triangle_labels : ∀ a b c l m n (i : Fin 5),
    Adj L a b → Adj L b c → Adj L c a →
    OnLine L a l → OnLine L b l → OnLine L a m → OnLine L c m →
    OnLine L b n → OnLine L c n →
    (LineType residue i a l m ↔ LineType residue i b l n)
  common_neighbors_in_plane : ∀ x y π, DistanceTwo L x y →
    OnPlane P x π → OnPlane P y π → ∀ u, Adj L x u → Adj L y u → OnPlane P u π
  marker_mem_core : ∀ π x, marker π ∈ coreAt P x ↔ OnPlane P x π

namespace Input
variable {h : IsTypeJ4 z} (d : Input h)

/-- The existing constructor, with all of its original algebraic premises. -/
def system : System G (Point d.P) :=
  systemOfLocalSubgroups z d.P.M d.t d.t_plane d.t_not_point d.t_sq
    d.faithful d.generate d.vertex_maximal d.plane_maximal d.edge_fixer

theorem system_adj_iff (a b : Point d.P) : d.system.graph.Adj a b ↔ Adj d.L a b :=
  Cosets.adj_iff_collinear d.P.M d.t d.L.G₂ d.t_not_point d.t_line d.line_transitive a b

theorem system_graph : d.system.graph = graph d.L := by
  ext a b
  exact d.system_adj_iff a b

theorem system_local_edge (a b : Point d.P) : d.system.localEdge a b ↔
    Adj d.L a b ∧ OnPlane d.P a (Cosets.vertex (centralizer z) 1) ∧
      OnPlane d.P b (Cosets.vertex (centralizer z) 1) := d.local_edge a b

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
