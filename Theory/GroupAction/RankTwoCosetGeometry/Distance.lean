module

public import Theory.GroupAction.RankTwoCosetGeometry
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Distances in rank-two coset geometry

Translation preserves distances and balls. A walk alternates its vertex type
at every step; consequently distance is even exactly between vertices of the
same type. Generation ensures that natural-valued distance is a genuine metric
distance. The extended-distance definition of balls also works without generation.

Source: Aschbacher–Smith, F.7.2 and the distance conventions used in F.7.8–14,
printed pp.311–315.
-/

@[expose] public section
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

private theorem edist_smul_le (g : G) (v w : Vertex F) :
    (graph F).edist (g • v) (g • w) ≤ (graph F).edist v w := by
  by_cases h : (graph F).Reachable v w
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
    rw [← hp]
    have hp' := (p.map (translationGraphIso F g).toHom).edist_le
    change (graph F).edist (g • v) (g • w) ≤ _ at hp'
    simpa only [SimpleGraph.Walk.length_map] using hp'
  · rw [SimpleGraph.edist_eq_top_of_not_reachable h]
    exact le_top

/-- Extended distances, including disconnection, are preserved by translation. -/
theorem edist_smul (g : G) (v w : Vertex F) :
    (graph F).edist (g • v) (g • w) = (graph F).edist v w := by
  apply le_antisymm (edist_smul_le F g v w)
  simpa only [inv_smul_smul] using edist_smul_le F g⁻¹ (g • v) (g • w)

/-- Natural-valued distances are preserved by translation. -/
theorem dist_smul (g : G) (v w : Vertex F) :
    (graph F).dist (g • v) (g • w) = (graph F).dist v w := by
  simp only [SimpleGraph.dist, edist_smul]

/-- The closed ball defined by actual finite graph distance. -/
def ball (v : Vertex F) (n : ℕ) : Set (Vertex F) :=
  {w | (graph F).edist v w ≤ n}

/-- Under generation this is exactly the source's distance-at-most ball. -/
theorem mem_ball_iff (hgen : F false ⊔ F true = ⊤) (v w : Vertex F) (n : ℕ) :
    w ∈ ball F v n ↔ (graph F).dist v w ≤ n := by
  change (graph F).edist v w ≤ (n : ℕ∞) ↔ _
  rw [← ((connected F hgen) v w).coe_dist_eq_edist, ENat.natCast_le_natCast]

@[simp] theorem center_mem_ball (v : Vertex F) (n : ℕ) : v ∈ ball F v n := by
  simp [ball]

@[simp] theorem mem_ball_zero (v w : Vertex F) : w ∈ ball F v 0 ↔ w = v := by
  simp only [ball, Set.mem_ofPred_eq, Nat.cast_zero, nonpos_iff_eq_zero,
    SimpleGraph.edist_eq_zero_iff]
  exact eq_comm

@[simp] theorem mem_ball_one (v w : Vertex F) :
    w ∈ ball F v 1 ↔ (graph F).Adj v w ∨ v = w := by
  simp only [ball, Set.mem_ofPred_eq, Nat.cast_one,
    SimpleGraph.edist_le_one_iff_adj_or_eq]

theorem ball_mono (v : Vertex F) {m n : ℕ} (h : m ≤ n) : ball F v m ⊆ ball F v n :=
  fun _ hw => hw.trans (ENat.natCast_le_natCast.mpr h)

/-- Equivariance of every closed ball, with both center and tested vertex translated. -/
@[simp] theorem smul_mem_ball (g : G) (v w : Vertex F) (n : ℕ) :
    g • w ∈ ball F (g • v) n ↔ w ∈ ball F v n := by
  simp only [ball, Set.mem_ofPred_eq, edist_smul]

/-- Adjacent centers give the containment used to compare successive ball kernels. -/
theorem ball_subset_succ {v w : Vertex F} (h : (graph F).Adj v w) (n : ℕ) :
    ball F w n ⊆ ball F v (n + 1) := by
  intro z hz
  change (graph F).edist v z ≤ ((n + 1 : ℕ) : ℕ∞)
  calc
    (graph F).edist v z ≤ (graph F).edist v w + (graph F).edist w z :=
      SimpleGraph.edist_triangle
    _ ≤ 1 + (n : ℕ∞) := add_le_add
      (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr h)) hz
    _ = ((n + 1 : ℕ) : ℕ∞) := by simp [add_comm]

/-- Every walk alternates types, without any connectedness assumption. -/
theorem even_walk_iff {v w : Vertex F} (p : (graph F).Walk v w) :
    Even p.length ↔ v.type = w.type := by
  induction p with
  | nil => simp
  | @cons v w z h p ih =>
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih]
    have ht := h.1
    cases hi : v.type <;> cases hj : w.type <;> cases hk : z.type <;> simp_all

/-- Distance parity detects the two orbits. -/
theorem even_dist_iff (hgen : F false ⊔ F true = ⊤) (v w : Vertex F) :
    Even ((graph F).dist v w) ↔ v.type = w.type := by
  obtain ⟨p, hp⟩ := (connected F hgen).exists_walk_length_eq_dist v w
  rw [← hp]
  exact even_walk_iff F p

theorem odd_dist_iff (hgen : F false ⊔ F true = ⊤) (v w : Vertex F) :
    Odd ((graph F).dist v w) ↔ v.type ≠ w.type := by
  rw [← Nat.not_even_iff_odd, even_dist_iff F hgen]

/-- Moving along one edge changes distance from a fixed vertex by exactly one. -/
theorem adjacent_dist_step (hgen : F false ⊔ F true = ⊤)
    (a : Vertex F) {v w : Vertex F} (h : (graph F).Adj v w) :
    (graph F).dist a w = (graph F).dist a v + 1 ∨
      (graph F).dist a v = (graph F).dist a w + 1 := by
  have hne : (graph F).dist a w ≠ (graph F).dist a v := by
    intro he
    have hp : (a.type = w.type) ↔ (a.type = v.type) := by
      rw [← even_dist_iff F hgen a w, ← even_dist_iff F hgen a v, he]
    have ht := h.1
    cases ha : a.type <;> cases hv : v.type <;> cases hw : w.type <;> simp_all
  rcases h.diff_dist_adj (u := a) with hd | hd | hd
  · exact (hne hd).elim
  · exact Or.inl hd
  · exact Or.inr (by omega)

/-- A noncentral vertex has a neighbor one step closer to the specified center. -/
theorem exists_predecessor (hgen : F false ⊔ F true = ⊤) (a v : Vertex F)
    (hne : a ≠ v) :
    ∃ w : Vertex F, (graph F).Adj v w ∧
      (graph F).dist a w + 1 = (graph F).dist a v := by
  obtain ⟨p, hp⟩ := (connected F hgen).exists_walk_length_eq_dist v a
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ w _ h p =>
    refine ⟨w, h, ?_⟩
    have hlen := SimpleGraph.dist_le p
    have ht := (connected F hgen).dist_triangle (u := v) (v := w) (w := a)
    have he : (graph F).dist v w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
    simp only [SimpleGraph.Walk.length_cons] at hp
    rw [he] at ht
    rw [SimpleGraph.dist_comm (u := a) (v := w), SimpleGraph.dist_comm (u := a) (v := v)]
    omega

end Subgroup.CosetGeometry.RankTwo
