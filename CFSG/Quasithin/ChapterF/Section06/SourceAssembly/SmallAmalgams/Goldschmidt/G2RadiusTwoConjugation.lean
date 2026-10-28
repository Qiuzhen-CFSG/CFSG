module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.G2RadiusTwoSixLabels

/-!
# The literal conjugation action on the six radius-two cosets

The two labels in each branch are distinct modulo the original neighboring
four-group. A selected label fixes its own binary branch and exchanges the
other two branches. Equivariance of the labels then makes conjugation of all
six cosets equal to the actual action on the six distance-two vertices.

These are the original source relations used to identify the quotient with
S₄ in Goldschmidt (1980), (6.9), printed pp.400--401.
-/

public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
namespace RadiusTwoSixLabels.Frame
variable {β : RankTwo.Vertex F} {f : BranchFrame F β} (r : RadiusTwoSixLabels.Frame f)

/-- The two labels in a branch remain distinct modulo the actual normal
four-group: their product has the branch label as its nontrivial square. -/
theorem pair_product_not_mem_neighborLabelGroup
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : CubicTreeAction F) (hβ : β.type ≠ c.side) (i : Fin 3) :
    c.label (r.u (i,0)) * c.label (r.u (i,1)) ∉ c.neighborLabelGroup β := by
  intro hp
  have hsq : (c.label (r.u (i,0)) * c.label (r.u (i,1))) ^ 2 = c.label (f.e i).val := by
    simpa only [commutatorElement_def, c.label_inv (r.vertex_type c h hβ (i,0)),
      c.label_inv (r.vertex_type c h hβ (i,1)), pow_two, mul_assoc] using
      r.pair_commutator c hr hs h hβ i
  let := c.radiusTwo_neighborLabelGroup_isKleinFour hr (by omega) h β hβ
  have hp1 := congrArg Subtype.val (IsKleinFour.mul_self
    (⟨_, hp⟩ : c.neighborLabelGroup β))
  have he : c.label (f.e i).val = 1 := hsq.symm.trans (by simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using hp1)
  have ho := c.order_two (f.e i).val (branch_type c hβ i)
  simp only [he, orderOf_one] at ho
  omega

/-- The actual chosen forward label fixes its entire two-point branch. -/
theorem label_fixes_branch (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 3 ≤ s) (h : CubicTreeAction F) (hβ : β.type ≠ c.side)
    (x : Fin 3 × ZMod 2) (b : ZMod 2) :
    c.label (r.u x) • f.point (x.1,b) = f.point (x.1,b) := by
  have hd : (RankTwo.graph F).dist (r.u x) (f.point (x.1,b)) ≤ 3 := by
    have he := h.tree.connected.dist_triangle
      (u := r.u x) (v := (f.e x.1).val) (w := f.point (x.1,b))
    rw [SimpleGraph.dist_comm (u := r.u x) (v := (f.e x.1).val), r.dist_two h x,
      dist_eq_one_iff_adj.mpr (f.point_adj (x.1,b))] at he
    exact he
  exact c.fixes_ball (r.u x) (r.vertex_type c h hβ x) (f.point (x.1,b))
    (by omega) (by omega)

private theorem permutation_three_fixed :
    ∀ (p : Equiv.Perm (Fin 3)) (i : Fin 3),
      (∀ j, p j = j ↔ j = i) → p = Equiv.swap (i + 1) (i + 2) := by decide

/-- The literal branch permutation of each of the six marked labels. -/
theorem label_branch_action (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 4 ≤ s) (h : CubicTreeAction F) (hβ : β.type ≠ c.side)
    (x : Fin 3 × ZMod 2) :
    f.branchAction ⟨c.label (r.u x),
      c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ x)⟩ =
        Equiv.swap (x.1 + 1) (x.1 + 2) := by
  apply permutation_three_fixed
  intro j
  have he := f.branchAction_eval
    ⟨c.label (r.u x), c.radiusTwo_second_le_stabilizer hr (by omega) β
      (r.mem_second c h hβ x)⟩ j
  constructor
  · intro hj
    by_contra hji
    have hneq : (f.e j).val ≠ (f.e x.1).val :=
      fun hh => hji (f.e.injective (Subtype.ext hh))
    have hβa : (RankTwo.graph F).Adj β (f.e x.1).val := (f.e x.1).property
    let p : BasedWalk (RankTwo.graph F) 4 (r.u x) :=
      ⟨⟨f.point x, (r.adj x).symm⟩, ⟨⟨(f.e x.1).val, (f.point_adj x).symm⟩,
        ⟨⟨β, hβa.symm⟩, ⟨⟨(f.e j).val, (f.e j).property⟩, PUnit.unit⟩⟩⟩⟩
    have hp : p.Nonbacktracking :=
      ⟨(r.ne x).symm, (f.point_ne_center x).symm, hneq, trivial⟩
    have hd : (RankTwo.graph F).dist (r.u x) (f.e j).val = 4 :=
      geodesic_of_nonbacktracking_of_cycle_bound h.tree.connected
        (N := 8) (fun _ _ hc => (h.tree.isAcyclic _ hc).elim) p hp (by decide)
    exact c.moves_sphere (r.u x) (r.vertex_type c h hβ x) (by omega)
      (f.e j).val (by omega) (by rw [hj] at he; exact he.symm)
  · rintro rfl
    apply f.e.injective
    apply Subtype.ext
    rw [he]
    exact c.fixes_ball (r.u x) (r.vertex_type c h hβ x) (f.e x.1).val
      (by rw [SimpleGraph.dist_comm, r.dist_two h x]; omega)
      (by rw [SimpleGraph.dist_comm, r.dist_two h x]; omega)

/-- A forward label has the same coset modulo the original neighboring
four-group as the selected label beyond that distance-two vertex. -/
theorem forward_label_difference_mem
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 3 ≤ s)
    (h : CubicTreeAction F) (hβ : β.type ≠ c.side)
    (x : Fin 3 × ZMod 2) {w : RankTwo.Vertex F}
    (hw : (RankTwo.graph F).Adj (f.point x) w) (hne : w ≠ (f.e x.1).val) :
    c.label w * (c.label (r.u x))⁻¹ ∈ c.neighborLabelGroup β := by
  have hzN : c.label (f.e x.1).val ∈ c.neighborLabelGroup β :=
    subset_closure ⟨(f.e x.1).val, (f.e x.1).property, rfl⟩
  rcases r.forward_label_cases c h hβ x hw hne with he | he
  · rw [he, mul_inv_cancel]
    exact one_mem _
  · rw [he, mul_inv_rev]
    have hc := c.radiusTwo_commute_of_dist_le_three hr hs (branch_type c hβ x.1)
      (r.vertex_type c h hβ x) (by rw [r.dist_two h x]; decide)
    rw [c.label_inv (branch_type c hβ x.1),
      c.label_inv (r.vertex_type c h hβ x), ← hc.eq, mul_assoc,
      c.label_mul_self (r.vertex_type c h hβ x), mul_one]
    exact hzN

/-- Conjugation of all six generator cosets is the literal action on the
six distance-two vertices, with no abstract permutation relabeling. -/
theorem conjugate_label_difference_mem
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 3 ≤ s)
    (h : CubicTreeAction F) (hβ : β.type ≠ c.side)
    (g : RankTwo.stabilizer F β) (x : Fin 3 × ZMod 2) :
    (g.val * c.label (r.u x) * g.val⁻¹) *
      (c.label (r.u (f.sphereAction h g x)))⁻¹ ∈ c.neighborLabelGroup β := by
  rw [← c.conjugate g.val (r.u x) (r.vertex_type c h hβ x)]
  apply r.forward_label_difference_mem c hr hs h hβ
  · rw [f.sphereAction_eval]
    exact (translationGraphIso F g.val).toHom.map_adj (r.adj x)
  · have he : (f.e (f.sphereAction h g x).1).val = g.val • (f.e x.1).val := by
      rw [f.sphereAction_block, f.branchAction_eval]
    rw [he]
    exact fun hh => r.ne x ((MulAction.toPerm g.val).injective hh)


end RadiusTwoSixLabels.Frame
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
