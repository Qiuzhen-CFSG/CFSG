module

public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.TriangleOrbit
public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph
public import Theory.SpecificGroups.OmegaSixThree.ModelComparison
public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleBase

/-!
# The concrete orthogonal uniqueness system

The local group is the setwise stabilizer of the three standard norm-minus-one
points. Ordered triangle transitivity supplies its permutations and the local
stabilizer orbits. The common-neighbor geometry then proves the three generation
identities of a uniqueness system. Faithfulness follows from simplicity and the
nontrivial point orbit.

Source: Aschbacher–Smith, F.5.7–F.5.8, pp.302–304.
-/

@[expose] public section

namespace OmegaSixThree.OrthogonalityGraph

open Theory.GroupTheory.GraphUniquenessSystem
open scoped Pointwise

local notation "M" => omegaPlusSixThree
local notation "x" => standardFirst
local notation "y" => standardSecond
local notation "z" => standardThird

/-- The literal projective triangle used in F.5. -/
def standardTriangle : Set Point := {x, y, z}

/-- The local subgroup preserves the standard triple setwise. -/
def triangleStabilizer : Subgroup M := MulAction.stabilizer M standardTriangle

theorem mem_triangleStabilizer_iff (g : M) :
    g ∈ triangleStabilizer ↔ (fun a : Point => g • a) '' standardTriangle = standardTriangle :=
  Iff.rfl

theorem triangleStabilizer_smul_mem {g : M} (hg : g ∈ triangleStabilizer)
    {a : Point} (ha : a ∈ standardTriangle) : g • a ∈ standardTriangle := by
  rw [← (mem_triangleStabilizer_iff g).mp hg]
  exact Set.mem_image_of_mem _ ha

private theorem local_transport (a b c : Point)
    (hab : graph.Adj a b) (hbc : graph.Adj b c) (hca : graph.Adj c a)
    (hset : ({a,b,c} : Set Point) = standardTriangle) :
    ∃ g : M, g ∈ triangleStabilizer ∧ g • x = a ∧ g • y = b ∧ g • z = c := by
  obtain ⟨g, hgx, hgy, hgz⟩ := exists_triangle_transport a b c hab hbc hca
  refine ⟨g, ?_, hgx, hgy, hgz⟩
  rw [mem_triangleStabilizer_iff]
  simpa only [standardTriangle, Set.image_insert_eq, Set.image_singleton, hgx, hgy, hgz]
    using hset

theorem exists_local_swap : ∃ g : M, g ∈ triangleStabilizer ∧
    g • x = y ∧ g • y = x ∧ g • z = z := by
  apply local_transport y x z standard_adjacent.1.symm
    standard_adjacent.2.2.symm standard_adjacent.2.1.symm
  ext a
  simp [standardTriangle, or_left_comm]

theorem exists_local_flip : ∃ g : M, g ∈ triangleStabilizer ∧
    g • x = x ∧ g • y = z ∧ g • z = y := by
  apply local_transport x z y standard_adjacent.2.2.symm
    standard_adjacent.2.1.symm standard_adjacent.1.symm
  ext a
  simp [standardTriangle, or_comm]

theorem vertex_transitive (a : Point) : ∃ g : M, g • x = a := by
  obtain ⟨b, hab, _⟩ := exists_common_neighbor a a
  obtain ⟨c, hac, hbc⟩ := exists_common_neighbor a b
  obtain ⟨g, hg, _, _⟩ := exists_triangle_transport a b c hab hbc hac.symm
  exact ⟨g, hg⟩

theorem ordered_edge_transitive (a b : Point) (hab : graph.Adj a b) :
    ∃ g : M, g • x = a ∧ g • y = b := by
  obtain ⟨c, hac, hbc⟩ := exists_common_neighbor a b
  obtain ⟨g, hgx, hgy, _⟩ := exists_triangle_transport a b c hab hbc hac.symm
  exact ⟨g, hgx, hgy⟩

theorem omega_faithful (g : M) (hg : ∀ a : Point, g • a = a) : g = 1 := by
  let := omega_simple
  let f := MulAction.toPermHom M Point
  have hker : f.ker = ⊥ := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · obtain ⟨t, _, htx, _, _⟩ := exists_local_swap
      have ht : f t = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top t)
      have hfix : t • x = x := congrArg (fun p : Equiv.Perm Point => p x) ht
      exact (standard_adjacent.1.ne (hfix.symm.trans htx)).elim
  apply (MonoidHom.ker_eq_bot_iff f).mp hker
  ext a
  exact (hg a).trans (one_smul M a).symm

private theorem mem_of_image {K : Subgroup M} {a : Point}
    (hstab : MulAction.stabilizer M a ≤ K) {g k : M}
    (hk : k ∈ K) (he : k • a = g • a) : g ∈ K := by
  have hc : k⁻¹ * g ∈ K := hstab (by
    change (k⁻¹ * g) • a = a
    rw [mul_smul, ← he, inv_smul_smul])
  simpa only [mul_inv_cancel_left] using K.mul_mem hk hc

theorem local_vertex_generate :
    triangleStabilizer ⊔ MulAction.stabilizer M x = ⊤ := by
  let K := triangleStabilizer ⊔ MulAction.stabilizer M x
  have hstab : MulAction.stabilizer M x ≤ K := le_sup_right
  obtain ⟨t, htH, htx, _, _⟩ := exists_local_swap
  have htK : t ∈ K := (show triangleStabilizer ≤ K from le_sup_left) htH
  have move (a : Point) (ha : graph.Adj x a) : ∃ k : M, k ∈ K ∧ k • x = a := by
    obtain ⟨b, hxb, hab⟩ := exists_common_neighbor x a
    obtain ⟨h, hhx, hhy, _⟩ := exists_triangle_transport x a b ha hab hxb.symm
    exact ⟨h*t, K.mul_mem (hstab hhx) htK, by rw [mul_smul, htx, hhy]⟩
  apply top_unique
  intro g _
  obtain ⟨a, hxa, hga⟩ := exists_common_neighbor x (g • x)
  obtain ⟨k, hk, hkx⟩ := move a hxa
  have hadj : graph.Adj x (k⁻¹ • (g • x)) := by
    simpa only [← hkx, inv_smul_smul] using omega_preserves k⁻¹ hga.symm
  obtain ⟨l, hl, hlx⟩ := move (k⁻¹ • (g • x)) hadj
  apply mem_of_image hstab (K.mul_mem hk hl)
  rw [mul_smul, hlx, smul_inv_smul]

theorem edge_local_vertex_generate :
    edgeFixer M x y ⊔ (triangleStabilizer ⊓ MulAction.stabilizer M x) =
      MulAction.stabilizer M x := by
  let K := edgeFixer M x y ⊔ (triangleStabilizer ⊓ MulAction.stabilizer M x)
  have hle : K ≤ MulAction.stabilizer M x := sup_le inf_le_left inf_le_right
  have hedge : edgeFixer M x y ≤ K := le_sup_left
  obtain ⟨t, htH, htx, hty, _⟩ := exists_local_flip
  have htK : t ∈ K := (show triangleStabilizer ⊓ MulAction.stabilizer M x ≤ K
    from le_sup_right) ⟨htH, htx⟩
  have move (a : Point) (hxa : graph.Adj x a) (hya : graph.Adj y a) :
      ∃ k : M, k ∈ K ∧ k • y = a := by
    obtain ⟨h, hhx, hhy, hhz⟩ := exists_triangle_transport x y a
      standard_adjacent.1 hya hxa.symm
    exact ⟨h*t, K.mul_mem (hedge ⟨hhx,hhy⟩) htK, by rw [mul_smul, hty, hhz]⟩
  apply le_antisymm hle
  intro g hg
  have hgx : g • x = x := hg
  have hxgy : graph.Adj x (g • y) := by
    simpa only [hgx] using omega_preserves g standard_adjacent.1
  obtain ⟨a, hxa, hya, hgya⟩ := edge_common_neighbor x y (g • y) standard_adjacent.1
  obtain ⟨k, hk, hky⟩ := move a hxa hya
  have hkx : k • x = x := hle hk
  have hxa' : graph.Adj x (k⁻¹ • (g • y)) := by
    have hxfix : k⁻¹ • x = x := by rw [inv_smul_eq_iff, hkx]
    simpa only [hxfix] using omega_preserves k⁻¹ hxgy
  have hya' : graph.Adj y (k⁻¹ • (g • y)) := by
    simpa only [← hky, inv_smul_smul] using omega_preserves k⁻¹ hgya.symm
  obtain ⟨l, hl, hly⟩ := move (k⁻¹ • (g • y)) hxa' hya'
  have hkl : k*l ∈ K := K.mul_mem hk hl
  have hkle : (k*l) • y = g • y := by rw [mul_smul, hly, smul_inv_smul]
  have hc : (k*l)⁻¹*g ∈ edgeFixer M x y := by
    constructor
    · change ((k*l)⁻¹*g) • x = x
      rw [mul_smul, hgx, inv_smul_eq_iff]
      exact (hle hkl).symm
    · change ((k*l)⁻¹*g) • y = y
      rw [mul_smul, ← hkle, inv_smul_smul]
  simpa only [mul_inv_cancel_left] using K.mul_mem hkl (hedge hc)

theorem local_edge_vertex_generate :
    (triangleStabilizer ⊓ edgeStabilizer M x y) ⊔
      (triangleStabilizer ⊓ MulAction.stabilizer M x) = triangleStabilizer := by
  let K := (triangleStabilizer ⊓ edgeStabilizer M x y) ⊔
    (triangleStabilizer ⊓ MulAction.stabilizer M x)
  have hle : K ≤ triangleStabilizer := sup_le inf_le_left inf_le_left
  obtain ⟨s, hsH, hsx, hsy, _⟩ := exists_local_swap
  obtain ⟨t, htH, htx, hty, _⟩ := exists_local_flip
  have hsK : s ∈ K := (show triangleStabilizer ⊓ edgeStabilizer M x y ≤ K
    from le_sup_left) ⟨hsH, Or.inr ⟨hsx,hsy⟩⟩
  have hlocal : triangleStabilizer ⊓ MulAction.stabilizer M x ≤ K := le_sup_right
  have htK : t ∈ K := hlocal ⟨htH,htx⟩
  apply le_antisymm hle
  intro g hg
  have hmem := triangleStabilizer_smul_mem hg (show x ∈ standardTriangle by simp [standardTriangle])
  have move : ∃ k : M, k ∈ K ∧ k • x = g • x := by
    simp only [standardTriangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hx | hy | hz
    · exact ⟨1, K.one_mem, by simpa only [one_smul] using hx.symm⟩
    · exact ⟨s, hsK, hsx.trans hy.symm⟩
    · exact ⟨t*s, K.mul_mem htK hsK, by rw [mul_smul, hsx, hty, hz]⟩
  obtain ⟨k, hk, he⟩ := move
  have hc : k⁻¹*g ∈ K := hlocal ⟨triangleStabilizer.mul_mem
      (triangleStabilizer.inv_mem (hle hk)) hg, by
    change (k⁻¹*g) • x = x
    rw [mul_smul, ← he, inv_smul_smul]⟩
  simpa only [mul_inv_cancel_left] using K.mul_mem hk hc

/-- The actual six-dimensional orthogonal model with its standard local group. -/
def modelSystem : System M Point where
  graph := graph
  H := triangleStabilizer
  «x» := x
  «y» := y
  adjacent := standard_adjacent.1
  preserves := omega_preserves
  faithful := omega_faithful
  vertex_transitive := vertex_transitive
  edge_transitive a b hab := by
    obtain ⟨g, hg⟩ := ordered_edge_transitive a b hab
    exact ⟨g, Or.inl hg⟩
  local_orbit := by
    obtain ⟨g, hgH, hgx, _, _⟩ := exists_local_swap
    exact ⟨⟨g,hgH⟩,hgx⟩
  generate := local_vertex_generate
  vertex_generate := edge_local_vertex_generate
  local_generate := local_edge_vertex_generate

@[simp] theorem modelSystem_graph : modelSystem.graph = graph := rfl
@[simp] theorem modelSystem_local : modelSystem.H = triangleStabilizer := rfl
@[simp] theorem modelSystem_first : modelSystem.x = x := rfl
@[simp] theorem modelSystem_second : modelSystem.y = y := rfl

theorem modelSystem_localEdge_iff (a b : Point) :
    modelSystem.localEdge a b ↔ a ≠ b ∧ a ∈ standardTriangle ∧ b ∈ standardTriangle := by
  constructor
  · rintro ⟨h, hab | hab⟩
    · obtain ⟨rfl,rfl⟩ := hab
      exact ⟨(omega_preserves h.val standard_adjacent.1).ne,
        triangleStabilizer_smul_mem h.property (by simp [standardTriangle]),
        triangleStabilizer_smul_mem h.property (by simp [standardTriangle])⟩
    · obtain ⟨rfl,rfl⟩ := hab
      exact ⟨(omega_preserves h.val standard_adjacent.1).ne.symm,
        triangleStabilizer_smul_mem h.property (by simp [standardTriangle]),
        triangleStabilizer_smul_mem h.property (by simp [standardTriangle])⟩
  · rintro ⟨hne,ha,hb⟩
    have make (a b c : Point) (hab : graph.Adj a b) (hbc : graph.Adj b c)
        (hca : graph.Adj c a) (hset : ({a,b,c} : Set Point) = standardTriangle) :
        modelSystem.localEdge a b := by
      obtain ⟨g,hgH,hgx,hgy,_⟩ := local_transport a b c hab hbc hca hset
      exact ⟨⟨g,hgH⟩,Or.inl ⟨hgx,hgy⟩⟩
    simp only [standardTriangle, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (hne rfl).elim
    · exact ⟨1,Or.inl ⟨one_smul M x,one_smul M y⟩⟩
    · obtain ⟨g,hgH,hgx,hgy,_⟩ := exists_local_flip
      exact ⟨⟨g,hgH⟩,Or.inl ⟨hgx,hgy⟩⟩
    · exact ⟨1,Or.inr ⟨one_smul M x,one_smul M y⟩⟩
    · exact (hne rfl).elim
    · apply make y z x standard_adjacent.2.1 standard_adjacent.2.2 standard_adjacent.1
      ext a
      simp only [standardTriangle, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · obtain ⟨g,hgH,hgx,hgy,_⟩ := exists_local_flip
      exact ⟨⟨g,hgH⟩,Or.inr ⟨hgx,hgy⟩⟩
    · apply make z y x standard_adjacent.2.1.symm standard_adjacent.1.symm
        standard_adjacent.2.2.symm
      ext a
      simp only [standardTriangle, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · exact (hne rfl).elim

/-- The standard triple is precisely the local edge orbit of the model system. -/
def modelLocalTriangle : modelSystem.LocalTriangle where
  third := z
  third_ne_x := standard_adjacent.2.2.ne
  third_ne_y := standard_adjacent.2.1.ne.symm
  localEdge_iff := modelSystem_localEdge_iff

@[simp] theorem modelLocalTriangle_vertices :
    modelLocalTriangle.vertices = standardTriangle := rfl

end OmegaSixThree.OrthogonalityGraph
