module

public import Theory.GroupAction.RankTwoCosetGeometry.Kernels

/-!
# The actual geometry of F.7

For subgroups G₁ and G₂ of an arbitrary ambient group, the acting group here
is literally their generated subgroup G₀ = G₁ ⊔ G₂. The vertices are the
two tagged coset spaces in G₀. All geometric clauses of F.7.3 are proved from
this construction. Finiteness is needed only for the eventual triviality of
ball kernels, and only the two vertex subgroups must be finite.

The source uses right cosets: `rightVertex` and `rightVertex_adj_iff` in the
reexported `Subgroup.CosetGeometry.RankTwo` API identify them by inversion,
with right translation g represented by left translation g⁻¹. In particular
the stabilizer is the source conjugate g⁻¹ Gᵢ g, not its opposite convention.

The final theorem retains precisely one group-theoretic premise: the common
normal core in G₀ is trivial. The F.7 assembly owner must discharge this from
F.7.1 using the local-core argument; this module does not assert that discharge.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.7.2–3,
printed pp.311–312 (PDF pp.322–323).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Section07.Geometry
open Subgroup
open Subgroup.CosetGeometry

variable {G : Type*} [Group G] (G₁ G₂ : Subgroup G)

/-- The two original subgroups, taken inside their actual generated group. -/
def family : Bool → Subgroup (G₁ ⊔ G₂ : Subgroup G)
  | false => G₁.subgroupOf (G₁ ⊔ G₂ : Subgroup G)
  | true => G₂.subgroupOf (G₁ ⊔ G₂ : Subgroup G)

abbrev Vertex := RankTwo.Vertex (family G₁ G₂)
abbrev graph := RankTwo.graph (family G₁ G₂)
abbrev base (i : Bool) := RankTwo.base (family G₁ G₂) i
abbrev vertexStabilizer (v : Vertex G₁ G₂) := RankTwo.stabilizer (family G₁ G₂) v
abbrev ballKernel (v : Vertex G₁ G₂) (n : ℕ) := RankTwo.ballKernel (family G₁ G₂) v n

/-- No extra generation hypothesis is needed after passing to G₀. -/
theorem family_generates : family G₁ G₂ false ⊔ family G₁ G₂ true = ⊤ := by
  apply (Subgroup.map_injective (show Function.Injective (G₁ ⊔ G₂ : Subgroup G).subtype from
    Subtype.val_injective))
  rw [Subgroup.map_sup, family, family, map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]

/-- F.7.3(1): the two type fibers are the two full orbits. -/
theorem vertex_orbits (i : Bool) :
    MulAction.orbit (G₁ ⊔ G₂ : Subgroup G) (base G₁ G₂ i) = {v : Vertex G₁ G₂ | v.type = i} := by
  ext v
  rw [MulAction.mem_orbit_iff, RankTwo.same_orbit_iff]
  exact eq_comm

/-- F.7.3(2): every unordered edge is a translate of the standard edge. -/
theorem edge_transitive {v w : Vertex G₁ G₂} (h : (graph G₁ G₂).Adj v w) :
    ∃ g : (G₁ ⊔ G₂ : Subgroup G), ({v, w} : Set (Vertex G₁ G₂)) =
      {g • base G₁ G₂ false, g • base G₁ G₂ true} :=
  RankTwo.edge_transitive (family G₁ G₂) h

/-- The stabilizer of that unordered edge is exactly the original intersection in G₀. -/
theorem standard_edge_stabilizer (g : (G₁ ⊔ G₂ : Subgroup G)) :
    ({g • base G₁ G₂ false, g • base G₁ G₂ true} : Set (Vertex G₁ G₂)) =
      {base G₁ G₂ false, base G₁ G₂ true} ↔ (g : G) ∈ G₁ ⊓ G₂ :=
  RankTwo.base_edge_stabilizer (family G₁ G₂) g

/-- F.7.3(3). -/
theorem connected : (graph G₁ G₂).Connected :=
  RankTwo.connected (family G₁ G₂) (family_generates G₁ G₂)

/-- F.7.3(4): stabilizers of the standard vertices are the original vertex groups. -/
theorem base_stabilizer (i : Bool) : vertexStabilizer G₁ G₂ (base G₁ G₂ i) = family G₁ G₂ i :=
  stabilizer_base (family G₁ G₂) i

/-- The first standard stabilizer maps back to exactly G₁ in the original ambient group. -/
theorem base_stabilizer_map_false :
    (vertexStabilizer G₁ G₂ (base G₁ G₂ false)).map (G₁ ⊔ G₂ : Subgroup G).subtype = G₁ := by
  rw [base_stabilizer]
  exact map_subgroupOf_eq_of_le le_sup_left

/-- The second standard stabilizer maps back to exactly G₂. -/
theorem base_stabilizer_map_true :
    (vertexStabilizer G₁ G₂ (base G₁ G₂ true)).map (G₁ ⊔ G₂ : Subgroup G).subtype = G₂ := by
  rw [base_stabilizer]
  exact map_subgroupOf_eq_of_le le_sup_right

/-- The right-coset stabilizer has the literal conjugation convention of F.7.2. -/
theorem right_coset_stabilizer (i : Bool) (g : (G₁ ⊔ G₂ : Subgroup G)) :
    vertexStabilizer G₁ G₂ (RankTwo.rightVertex (family G₁ G₂) i g) =
      (family G₁ G₂ i).map (MulAut.conj g⁻¹).toMonoidHom :=
  RankTwo.stabilizer_rightVertex (family G₁ G₂) i g

/-- F.7.3(5). -/
theorem local_transitivity {v w z : Vertex G₁ G₂}
    (hw : (graph G₁ G₂).Adj v w) (hz : (graph G₁ G₂).Adj v z) :
    ∃ g ∈ vertexStabilizer G₁ G₂ v, g • w = z :=
  RankTwo.locally_transitive (family G₁ G₂) hw hz

/-- F.7.3(6), with normality in the vertex stabilizer. -/
theorem ballKernel_normal (v : Vertex G₁ G₂) (n : ℕ) :
    ((ballKernel G₁ G₂ v n).subgroupOf (vertexStabilizer G₁ G₂ v)).Normal :=
  RankTwo.ballKernel_normal (family G₁ G₂) v n

/-- F.7.3(7), with the core taken inside the specified vertex group. -/
theorem ballKernel_one_core (i : Bool) :
    (ballKernel G₁ G₂ (base G₁ G₂ i) 1).subgroupOf (family G₁ G₂ i) =
      (((G₁ ⊓ G₂).subgroupOf (G₁ ⊔ G₂ : Subgroup G)).subgroupOf (family G₁ G₂ i)).normalCore := by
  have h := RankTwo.base_ballKernel_one (family G₁ G₂) i
  exact h

/-- The kernel is the common normal core in G₀, not a core in the larger ambient G. -/
theorem global_kernel :
    (MulAction.toPermHom (G₁ ⊔ G₂ : Subgroup G) (Vertex G₁ G₂)).ker =
      ((G₁ ⊓ G₂).subgroupOf (G₁ ⊔ G₂ : Subgroup G)).normalCore :=
  RankTwo.global_kernel (family G₁ G₂)

/-- The global action kernel, placed in the original ambient group. -/
def ambientKernel : Subgroup G :=
  (MulAction.toPermHom (G₁ ⊔ G₂ : Subgroup G) (Vertex G₁ G₂)).ker.map (G₁ ⊔ G₂).subtype

/-- The global kernel is contained in both original vertex groups. -/
theorem ambientKernel_le : ambientKernel G₁ G₂ ≤ G₁ ⊓ G₂ := by
  unfold ambientKernel
  rw [global_kernel]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ((G₁ ⊓ G₂).subgroupOf (G₁ ⊔ G₂)).normalCore_le hy

/-- The limiting kernel is normal in the generated group, expressed by its ambient normalizer. -/
theorem generated_normalizes_ambientKernel :
    G₁ ⊔ G₂ ≤ normalizer (ambientKernel G₁ G₂ : Set G) := by
  let K := (MulAction.toPermHom (G₁ ⊔ G₂ : Subgroup G) (Vertex G₁ G₂)).ker
  have h := K.le_normalizer_map (G₁ ⊔ G₂).subtype
  rw [normalizer_eq_top_iff.mpr (inferInstance : K.Normal),
    ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

/-- The precise first relative-normality input of the independent F.7.3(8) algebra. -/
theorem ambientKernel_normal_left : ((ambientKernel G₁ G₂).subgroupOf G₁).Normal :=
  normal_subgroupOf_of_le_normalizer
    (le_sup_left.trans (generated_normalizes_ambientKernel G₁ G₂))

/-- The precise second relative-normality input of the independent F.7.3(8) algebra. -/
theorem ambientKernel_normal_right : ((ambientKernel G₁ G₂).subgroupOf G₂).Normal :=
  normal_subgroupOf_of_le_normalizer
    (le_sup_right.trans (generated_normalizes_ambientKernel G₁ G₂))

/-- Every ball-kernel filtration has this same limiting ambient subgroup. -/
theorem ambientKernel_eq_map_iInf (v : Vertex G₁ G₂) :
    ambientKernel G₁ G₂ = (⨅ n, ballKernel G₁ G₂ v n).map (G₁ ⊔ G₂).subtype := by
  rw [RankTwo.iInf_ballKernel (family G₁ G₂) (family_generates G₁ G₂)]
  rfl

/-- Parity in the actual source graph detects the two vertex orbits. -/
theorem even_distance (v w : Vertex G₁ G₂) :
    Even ((graph G₁ G₂).dist v w) ↔ v.type = w.type :=
  RankTwo.even_dist_iff (family G₁ G₂) (family_generates G₁ G₂) v w

variable [Finite G₁] [Finite G₂]

instance finite_family (i : Bool) : Finite (family G₁ G₂ i) := by
  cases i
  · exact Finite.of_equiv G₁ (subgroupOfEquivOfLe (H := G₁) le_sup_left).symm.toEquiv
  · exact Finite.of_equiv G₂ (subgroupOfEquivOfLe (H := G₂) le_sup_right).symm.toEquiv

/-- The geometric part of F.7.3(8). The common-core premise is the remaining
group-theoretic obligation of the source-theorem assembly, not an assumed ball conclusion. -/
theorem uniform_trivial_ballKernel_of_core_free
    (hcore : ((G₁ ⊓ G₂).subgroupOf (G₁ ⊔ G₂ : Subgroup G)).normalCore = ⊥) :
    ∃ n : ℕ, 0 < n ∧ ∀ v : Vertex G₁ G₂, ballKernel G₁ G₂ v n = ⊥ := by
  obtain ⟨n, hn, h⟩ := RankTwo.uniform_trivial_ballKernel (family G₁ G₂)
    (family_generates G₁ G₂) ((global_kernel G₁ G₂).trans hcore)
  exact ⟨n, hn, fun v => h v n le_rfl⟩

/-- Assembly with `LocalCores.lemma_F_7_3_eight_algebra` needs no change of
ambient groups: its conclusion on `ambientKernel` supplies the remaining input. -/
theorem uniform_trivial_ballKernel_of_ambientKernel_eq_bot
    (hker : ambientKernel G₁ G₂ = ⊥) :
    ∃ n : ℕ, 0 < n ∧ ∀ v : Vertex G₁ G₂, ballKernel G₁ G₂ v n = ⊥ := by
  have hk : (MulAction.toPermHom (G₁ ⊔ G₂ : Subgroup G) (Vertex G₁ G₂)).ker = ⊥ := by
    apply Subgroup.map_injective (show Function.Injective (G₁ ⊔ G₂).subtype from
      Subtype.val_injective)
    simpa only [ambientKernel, Subgroup.map_bot] using hker
  obtain ⟨n, hn, h⟩ := RankTwo.uniform_trivial_ballKernel (family G₁ G₂)
    (family_generates G₁ G₂) hk
  exact ⟨n, hn, fun v => h v n le_rfl⟩

end CFSG.Quasithin.ChapterF.Section07.Geometry
