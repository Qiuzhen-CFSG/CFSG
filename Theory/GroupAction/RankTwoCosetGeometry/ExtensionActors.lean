module
public import Theory.GroupAction.CubicTree.TotalSingularity
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Theory.GroupAction.FivePointOrderFour

/-!
# Local actors extending cubic--quintic paths

At a cubic endpoint, any path fixer outside the radius-one kernel exchanges
the two forward neighbors. At a quintic endpoint, a fixer whose local action
has order four cycles the four forward neighbors. The latter condition is
stated using the literal ball kernel, so the ambient element need not have
order four. Neither result requires a finite graph or ambient group.

Source: the nonbacktracking path convention of Aschbacher--Smith F.3.2,
p.270; Goldschmidt (1980), the local extension argument after (2.12), p.384.
The degree-five permutation step is the separately checked five-point lemma.
-/

public noncomputable section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

private theorem graph_action : GraphAction (graph F) G :=
  ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj h⟩

private def neighborPerm {v : Vertex F} (a : G) (ha : a • v = v) :
    Equiv.Perm ((graph F).neighborSet v) where
  toFun z := ⟨a • z.val, by
    change (graph F).Adj v (a • z.val)
    have h := (graph_action F).map_adj a z.property
    simpa only [ha] using h⟩
  invFun z := ⟨a⁻¹ • z.val, by
    change (graph F).Adj v (a⁻¹ • z.val)
    have h := (graph_action F).map_adj a⁻¹ z.property
    simpa only [inv_smul_eq_iff.mpr ha.symm] using h⟩
  left_inv z := Subtype.ext (inv_smul_smul a z.val)
  right_inv z := Subtype.ext (smul_inv_smul a z.val)

private theorem neighborPerm_pow {v : Vertex F} (a : G) (ha : a • v = v)
    (n : ℕ) (z : (graph F).neighborSet v) :
    ((neighborPerm F a ha ^ n) z).val = a ^ n • z.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    change a • ((neighborPerm F a ha ^ n) z).val = _
    rw [ih, pow_succ', mul_smul]

/-- A four-cycle in the actual local action makes the path fixer transitive
on its four forward extensions. The ambient element itself may have larger order. -/
theorem rightRegular_of_quintic_kernel_actor
    {n : ℕ} {x : Vertex F} (p : BasedWalk (graph F) (n + 1) x)
    (hdegree : Nat.card ((graph F).neighborSet p.endpoint) = 5)
    (a : G) (ha : a ∈ pathStabilizer F p)
    (hfour : a ^ 4 ∈ ballKernel F p.endpoint 1)
    (hsquare : a ^ 2 ∉ ballKernel F p.endpoint 1) :
    RightRegular (A := G) p := by
  have hfix : p.vertices.map (a • ·) = p.vertices := by
    simpa only [List.map_id] using
      (List.map_congr_left (f := fun y => a • y) (g := id) ha)
  have hend : a • p.endpoint = p.endpoint :=
    endpoint_smul_of_vertices (graph_action F) a p p hfix
  have hprev : a • p.penultimate = p.penultimate := by
    have hh := congrArg (List.take (n + 1)) hfix
    rw [← List.map_take, ← BasedWalk.vertices_take n (Nat.le_succ n) p] at hh
    have ht := endpoint_smul_of_vertices (graph_action F) a
      (p.take n (Nat.le_succ n)) (p.take n (Nat.le_succ n)) hh
    simpa only [BasedWalk.endpoint_take_penultimate] using ht
  let : Finite ((graph F).neighborSet p.endpoint) :=
    Nat.finite_of_card_ne_zero (by rw [hdegree]; decide)
  let q := neighborPerm F a hend
  have qfour : q ^ 4 = 1 := by
    apply Equiv.Perm.ext
    intro z
    apply Subtype.ext
    rw [neighborPerm_pow]
    exact hfour z ((mem_ball_one F _ _).mpr (Or.inl z.property))
  have qsquare : q ^ 2 ≠ 1 := by
    intro hh
    apply hsquare
    intro z hz
    rcases (mem_ball_one F _ _).mp hz with hz | rfl
    · have he := congrArg (fun f : Equiv.Perm ((graph F).neighborSet p.endpoint) =>
        (f ⟨z, hz⟩).val) hh
      simpa only [q, neighborPerm_pow, Equiv.Perm.one_apply] using he
    · simp only [pow_two, mul_smul, hend]
  intro z w hz hw
  let r : (graph F).neighborSet p.endpoint :=
    ⟨p.penultimate, p.adj_penultimate_endpoint.symm⟩
  obtain ⟨k, hk⟩ := Equiv.Perm.exists_pow_apply_eq_of_order_four_card_five
    hdegree q qfour qsquare (root := r)
    (left := ⟨z, hz.1⟩) (right := ⟨w, hw.1⟩)
    (Subtype.ext hprev)
    (fun he => hz.2 (congrArg Subtype.val he))
    (fun he => hw.2 (congrArg Subtype.val he))
  refine ⟨a ^ k.val, (pathStabilizer F p).pow_mem ha _, ?_⟩
  exact (neighborPerm_pow F a hend k.val ⟨z, hz.1⟩).symm.trans
    (congrArg Subtype.val hk)

/-- At a cubic endpoint, escape from the local kernel is enough to exchange
the two forward neighbors, while fixing the entire original path. -/
theorem rightRegular_of_cubic_kernel_escape
    {n : ℕ} {x : Vertex F} (p : BasedWalk (graph F) (n + 1) x)
    (hdegree : Nat.card ((graph F).neighborSet p.endpoint) = 3)
    (ha : ¬ pathStabilizer F p ≤ ballKernel F p.endpoint 1) :
    RightRegular (A := G) p := by
  classical
  obtain ⟨a, ha, hnot⟩ := SetLike.not_le_iff_exists.mp ha
  have hfix : p.vertices.map (a • ·) = p.vertices := by
    simpa only [List.map_id] using
      (List.map_congr_left (f := fun y => a • y) (g := id) ha)
  have hend : a • p.endpoint = p.endpoint :=
    endpoint_smul_of_vertices (graph_action F) a p p hfix
  have hprev : a • p.penultimate = p.penultimate := by
    have hh := congrArg (List.take (n + 1)) hfix
    rw [← List.map_take, ← BasedWalk.vertices_take n (Nat.le_succ n) p] at hh
    have ht := endpoint_smul_of_vertices (graph_action F) a
      (p.take n (Nat.le_succ n)) (p.take n (Nat.le_succ n)) hh
    simpa only [BasedWalk.endpoint_take_penultimate] using ht
  have hex : ∃ z ∈ ball F p.endpoint 1, a • z ≠ z := by
    simpa only [mem_ballKernel, not_forall, Classical.not_imp, exists_prop] using hnot
  obtain ⟨z, hz, hm⟩ := hex
  rcases (mem_ball_one F _ _).mp hz with hz | rfl
  · exact rightRegular_of_moved_forward (graph_action F) p hdegree a ha
      ⟨hz, fun he => hm (he ▸ hprev)⟩ hm
  · exact (hm hend).elim
end Subgroup.CosetGeometry.RankTwo
