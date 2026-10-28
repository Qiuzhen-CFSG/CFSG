module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsStructure

/-!
# Source core generators on an arbitrary three-arm frame

Choose one depth-three labelled vertex in each branch at an unlabelled
vertex. The six-arc formula identifies the pairwise commutators with the
adjacent central labels. These relations generate a group of order 32;
the proved radius-three order identifies it with the literal source core.
This permits choosing the frame to be a cubic actor's orbit.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the
radius-three calculation in (6.12), printed p.406.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
open scoped commutatorElement
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem neighbor_side (d : CanonicalLabelSetup F s)
    {v a : RankTwo.Vertex F} (hv : v.type ≠ d.side)
    (ha : (RankTwo.graph F).Adj v a) : a.type = d.side := by
  have hn := ha.1
  cases h0 : v.type <;> cases h1 : a.type <;> cases h2 : d.side <;> simp_all

/-- Every compatible three-arm choice gives the literal marked source core. -/
theorem LocalRelations.radiusThree_arms_generators
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    {v : RankTwo.Vertex F} (hv : v.type ≠ d.side)
    (u w : Fin 3 → RankTwo.Vertex F)
    (hadj : ∀ i, (RankTwo.graph F).Adj v (u i))
    (hdistinct0 : ∀ i j, i ≠ j → u i ≠ u j)
    (hwtype : ∀ i, (w i).type = d.side)
    (hdist : ∀ i, (RankTwo.graph F).dist v (w i) = 3)
    (hnear : ∀ i, (RankTwo.graph F).dist (u i) (w i) = 2) :
    ThreeInvolutionFourCommutators.Relations (d.label (w 0)) (d.label (w 1))
      (d.label (w 2)) (d.label (u 2)) (d.label (u 1)) ∧
      closure ({d.label (w 0),d.label (w 1),d.label (w 2)} : Set G) = d.labelBall v 3 := by
  let t := h.action.toCubicTreeAction
  have hex (i : Fin 3) : ∃ c, (RankTwo.graph F).Adj (u i) c ∧
      (RankTwo.graph F).Adj c (w i) := by
    obtain ⟨_, c, hc, hw⟩ := (DistanceTwoGeometry.dist_eq_two_iff t.tree).mp (hnear i)
    exact ⟨c, hc, hw⟩
  choose c hc hw using hex
  have hcne (i : Fin 3) : c i ≠ v := by
    intro he
    have hh : (RankTwo.graph F).dist v (w i) = 1 :=
      dist_eq_one_iff_adj.mpr (he ▸ hw i)
    rw [hdist] at hh
    omega
  have hwne (i : Fin 3) : w i ≠ u i := by
    intro he
    have hh := hnear i
    rw [he, dist_self] at hh
    omega
  have hsix (i j : Fin 3) (hij : i ≠ j) :
      ⁅d.label (w i),d.label (w j)⁆ = d.label (u i) * d.label (u j) := by
    let p : BasedWalk (RankTwo.graph F) 6 (w i) :=
      ⟨⟨c i, (hw i).symm⟩, ⟨⟨u i, (hc i).symm⟩,
        ⟨⟨v, (hadj i).symm⟩, ⟨⟨u j, hadj j⟩,
          ⟨⟨c j, hc j⟩, ⟨⟨w j, hw j⟩, PUnit.unit⟩⟩⟩⟩⟩⟩
    have hp : p.Nonbacktracking :=
      ⟨(hwne i).symm, (hcne i).symm, (hdistinct0 i j hij).symm, hcne j, hwne j, trivial⟩
    have hpath : p.toWalk.IsPath := isPath_of_nonbacktracking_of_cycle_bound
      (N := 6) (fun _ _ hcycle => (t.tree.isAcyclic _ hcycle).elim) p hp le_rfl
    exact r.six_arc (w i) (w j) p.toWalk (hwtype i) hpath rfl
  let a : Fin 3 → G := fun i => d.label (u i)
  let x : Fin 3 → G := fun i => d.label (w i)
  have hat (i : Fin 3) : (u i).type = d.side := neighbor_side d hv (hadj i)
  have hxt := hwtype
  have hao (i : Fin 3) : orderOf (a i) = 2 := d.order_two _ (hat i)
  have hxo (i : Fin 3) : x i ^ 2 = 1 := by
    simpa only [x, d.order_two _ (hxt i)] using pow_orderOf_eq_one (x i)
  have ha2 (i : Fin 3) : a i * a i = 1 := d.label_mul_self (hat i)
  have hani (i : Fin 3) : a i ≠ 1 := by
    intro he
    have hh := hao i
    rw [he, orderOf_one] at hh
    omega
  have hdistinct (i j : Fin 3) (hij : i ≠ j) : u i ≠ u j :=
    hdistinct0 i j hij
  have hp : a 0 * a 1 * a 2 = 1 := d.neighbor_product v _ _ _
    (hadj 0) (hadj 1) (hadj 2)
    (hdistinct 0 1 (by decide)) (hdistinct 0 2 (by decide)) (hdistinct 1 2 (by decide))
    (hat 0)
  have h01 : a 0 * a 1 = a 2 := by
    simpa only [a, d.label_inv (hat 2)] using mul_eq_one_iff_eq_inv.mp hp
  have h02 : a 0 * a 2 = a 1 := by rw [← h01, ← mul_assoc, ha2, one_mul]
  have hac (i j : Fin 3) : Commute (a i) (a j) := by
    have hd : (RankTwo.graph F).dist (u i) (u j) ≤ 2 := by
      have hh := t.tree.connected.dist_triangle (u := u i) (v := v)
        (w := u j)
      simpa only [dist_eq_one_iff_adj.mpr (hadj i).symm,
        dist_eq_one_iff_adj.mpr (hadj j)] using hh
    exact d.labels_commute_of_dist_le (hat i) (hat j) (by omega) (by have := h.five_le; omega)
  have h12 : a 1 * a 2 = a 0 := by rw [← h01, ← mul_assoc, (hac 1 0).eq, mul_assoc, ha2, mul_one]
  have ha21 : a 2 ≠ a 1 := by
    intro he
    apply hani 0
    apply mul_right_cancel (b := a 1)
    simpa only [one_mul] using h01.trans he
  have hxcomm (i j : Fin 3) (hij : i ≠ j) : ⁅x i,x j⁆ = a i * a j :=
    hsix i j hij
  have hax (i j : Fin 3) : Commute (a i) (x j) := by
    have hd : (RankTwo.graph F).dist (u i) (w j) ≤ 4 := by
      have hh := t.tree.connected.dist_triangle (u := u i) (v := v) (w := w j)
      simpa only [dist_eq_one_iff_adj.mpr (hadj i).symm,
        hdist j] using hh
    exact d.labels_commute_of_dist_le (hat i) (hxt j) (by omega) (by have := h.five_le; omega)
  have hrelations : ThreeInvolutionFourCommutators.Relations
      (x 0) (x 1) (x 2) (a 2) (a 1) := {
    x_sq := hxo 0
    y_sq := hxo 1
    z_sq := hxo 2
    a_order := hao 2
    b_order := hao 1
    a_ne_b := ha21
    xy := (hxcomm 0 1 (by decide)).trans h01
    xz := (hxcomm 0 2 (by decide)).trans h02
    yz := by rw [(hxcomm 1 2 (by decide)), h12, (hac 2 1).eq, h12]
    bx := hax 1 0
    by_ := hax 1 1
    bz := hax 1 2 }
  refine ⟨hrelations, ?_⟩
  have hcard := r.radiusThree_card hr v hv
  let : Finite (d.labelBall v 3) := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  apply eq_of_le_of_card_ge
  · apply (closure_le _).mpr
    rintro y (rfl | rfl | rfl)
    · exact d.label_mem_labelBall (hxt 0) (le_of_eq (hdist 0))
    · exact d.label_mem_labelBall (hxt 1) (le_of_eq (hdist 1))
    · exact d.label_mem_labelBall (hxt 2) (le_of_eq (hdist 2))
  · rw [hrelations.card, hcard]

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
