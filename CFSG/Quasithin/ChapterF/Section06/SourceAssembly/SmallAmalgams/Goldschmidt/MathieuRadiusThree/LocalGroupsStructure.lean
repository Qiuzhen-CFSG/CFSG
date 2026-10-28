module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsCore
public import Theory.Mathieu.M12.ExceptionalParabolics.SourceRecognitionCore

/-!
# Marked generators of the radius-three label core

The three arms at the unlabelled vertex provide a generating triple satisfying
exactly the order-thirty-two recognition relations. Its closure is the full
radius-three label group because both have order thirty-two. Thus any concrete
realization of these relations recognizes the literal source group.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12), printed p.405, the generators `w₁,w₂,w₃` of the radius-three group.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
open scoped commutatorElement
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem exists_forward (h : CubicTreeAction F) (v a : RankTwo.Vertex F) :
    ∃ u, (RankTwo.graph F).Adj v u ∧ u ≠ a := by
  by_contra! hh
  have hi : Subsingleton ((RankTwo.graph F).neighborSet v) := ⟨fun x y =>
    Subtype.ext ((hh x x.property).trans (hh y y.property).symm)⟩
  have hc : Nat.card ((RankTwo.graph F).neighborSet v) ≤ 1 := by
    let f : (RankTwo.graph F).neighborSet v → Unit := fun _ => ()
    simpa using Nat.card_le_card_of_injective f (fun x y _ => Subsingleton.elim _ _)
  rw [h.card_neighbor v] at hc
  omega

private theorem neighbor_side (d : CanonicalLabelSetup F s)
    {v a : RankTwo.Vertex F} (hv : v.type ≠ d.side)
    (ha : (RankTwo.graph F).Adj v a) : a.type = d.side := by
  have hn := ha.1
  cases h0 : v.type <;> cases h1 : a.type <;> cases h2 : d.side <;> simp_all

private theorem frame_dist_three (h : CubicTreeAction F)
    {v : RankTwo.Vertex F} (f : BranchFrame F v)
    (w : Fin 3 → RankTwo.Vertex F)
    (hw : ∀ i, (RankTwo.graph F).Adj (f.c i) (w i))
    (hne : ∀ i, w i ≠ (f.e i).val) (i : Fin 3) :
    (RankTwo.graph F).dist v (w i) = 3 := by
  let p : BasedWalk (RankTwo.graph F) 3 v :=
    ⟨⟨(f.e i).val, (f.e i).property⟩,
      ⟨⟨f.c i, f.c_adj i⟩, ⟨⟨w i, hw i⟩, PUnit.unit⟩⟩⟩
  have hp : p.Nonbacktracking := ⟨f.c_ne_center i, hne i, trivial⟩
  exact geodesic_of_nonbacktracking_of_cycle_bound h.tree.connected
    (N := 6) (fun _ _ hc => (h.tree.isAcyclic _ hc).elim) p hp (by decide)

private theorem frame_six_commutator
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) {v : RankTwo.Vertex F} (hv : v.type ≠ d.side)
    (f : BranchFrame F v) (w : Fin 3 → RankTwo.Vertex F)
    (hw : ∀ i, (RankTwo.graph F).Adj (f.c i) (w i))
    (hne : ∀ i, w i ≠ (f.e i).val) {i j : Fin 3} (hij : i ≠ j) :
    ⁅d.label (w i), d.label (w j)⁆ = d.label (f.e i).val * d.label (f.e j).val := by
  let t := h.action.toCubicTreeAction
  have hadj (k : Fin 3) : (RankTwo.graph F).Adj v (f.e k).val := (f.e k).property
  have hmid : (f.e i).val ≠ (f.e j).val := fun he =>
    hij (f.e.injective (Subtype.ext he))
  let p : BasedWalk (RankTwo.graph F) 6 (w i) :=
    ⟨⟨f.c i, (hw i).symm⟩, ⟨⟨(f.e i).val, (f.c_adj i).symm⟩,
      ⟨⟨v, (hadj i).symm⟩, ⟨⟨(f.e j).val, hadj j⟩,
        ⟨⟨f.c j, f.c_adj j⟩, ⟨⟨w j, hw j⟩, PUnit.unit⟩⟩⟩⟩⟩⟩
  have hp : p.Nonbacktracking :=
    ⟨(hne i).symm, (f.c_ne_center i).symm, hmid.symm, f.c_ne_center j, hne j, trivial⟩
  have hpath : p.toWalk.IsPath := isPath_of_nonbacktracking_of_cycle_bound
    (N := 7) (fun _ _ hc => (t.tree.isAcyclic _ hc).elim) p hp (by decide)
  have hd : (RankTwo.graph F).dist (f.e i).val (w i) = 2 :=
    (DistanceTwoGeometry.dist_eq_two_iff t.tree).mpr
      ⟨(hne i).symm, f.c i, f.c_adj i, hw i⟩
  have htype : (w i).type = d.side :=
    ((RankTwo.even_dist_iff F t.generated _ _).mp (by rw [hd]; decide)).symm.trans
      (neighbor_side d hv (f.e i).property)
  exact r.six_arc (w i) (w j) p.toWalk htype hpath rfl

/-- The actual radius-three group has the marked three-involution presentation. -/
theorem LocalRelations.radiusThree_generators
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side) :
    ∃ x y z a b : G, ThreeInvolutionFourCommutators.Relations x y z a b ∧
      closure ({x,y,z} : Set G) = d.labelBall v 3 := by
  let t := h.action.toCubicTreeAction
  obtain ⟨f⟩ := t.exists_branchFrame v
  have hadj (i : Fin 3) : (RankTwo.graph F).Adj v (f.e i).val := (f.e i).property
  choose w hw hne using fun i : Fin 3 => exists_forward t (f.c i) (f.e i).val
  let a : Fin 3 → G := fun i => d.label (f.e i).val
  let x : Fin 3 → G := fun i => d.label (w i)
  have hat (i : Fin 3) : (f.e i).val.type = d.side := neighbor_side d hv (f.e i).property
  have hxt (i : Fin 3) : (w i).type = d.side := by
    have hd : (RankTwo.graph F).dist (f.e i).val (w i) = 2 :=
      (DistanceTwoGeometry.dist_eq_two_iff t.tree).mpr
        ⟨(hne i).symm, f.c i, f.c_adj i, hw i⟩
    exact ((RankTwo.even_dist_iff F t.generated _ _).mp
      (by rw [hd]; decide)).symm.trans (hat i)
  have hao (i : Fin 3) : orderOf (a i) = 2 := d.order_two _ (hat i)
  have hxo (i : Fin 3) : x i ^ 2 = 1 := by
    simpa only [x, d.order_two _ (hxt i)] using pow_orderOf_eq_one (x i)
  have ha2 (i : Fin 3) : a i * a i = 1 := d.label_mul_self (hat i)
  have hani (i : Fin 3) : a i ≠ 1 := by
    intro he
    have hh := hao i
    rw [he, orderOf_one] at hh
    omega
  have hdistinct (i j : Fin 3) (hij : i ≠ j) : (f.e i).val ≠ (f.e j).val :=
    fun he => hij (f.e.injective (Subtype.ext he))
  have hp : a 0 * a 1 * a 2 = 1 := d.neighbor_product v _ _ _
    (f.e 0).property (f.e 1).property (f.e 2).property
    (hdistinct 0 1 (by decide)) (hdistinct 0 2 (by decide)) (hdistinct 1 2 (by decide))
    (hat 0)
  have h01 : a 0 * a 1 = a 2 := by
    simpa only [a, d.label_inv (hat 2)] using mul_eq_one_iff_eq_inv.mp hp
  have h02 : a 0 * a 2 = a 1 := by rw [← h01, ← mul_assoc, ha2, one_mul]
  have hac (i j : Fin 3) : Commute (a i) (a j) := by
    have hd : (RankTwo.graph F).dist (f.e i).val (f.e j).val ≤ 2 := by
      have hh := t.tree.connected.dist_triangle (u := (f.e i).val) (v := v)
        (w := (f.e j).val)
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
    frame_six_commutator r hv f w hw hne hij
  have hax (i j : Fin 3) : Commute (a i) (x j) := by
    have hd : (RankTwo.graph F).dist (f.e i).val (w j) ≤ 4 := by
      have hh := t.tree.connected.dist_triangle (u := (f.e i).val) (v := v) (w := w j)
      simpa only [dist_eq_one_iff_adj.mpr (hadj i).symm,
        frame_dist_three t f w hw hne j] using hh
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
  refine ⟨x 0, x 1, x 2, a 2, a 1, hrelations, ?_⟩
  have hcard := r.radiusThree_card hr v hv
  let : Finite (d.labelBall v 3) := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  apply eq_of_le_of_card_ge
  · apply (closure_le _).mpr
    rintro y (rfl | rfl | rfl)
    · exact d.label_mem_labelBall (hxt 0) (le_of_eq (frame_dist_three t f w hw hne 0))
    · exact d.label_mem_labelBall (hxt 1) (le_of_eq (frame_dist_three t f w hw hne 1))
    · exact d.label_mem_labelBall (hxt 2) (le_of_eq (frame_dist_three t f w hw hne 2))
  · rw [hrelations.card, hcard]

/-- A concrete realization of the three relations identifies the literal
radius-three source group, with no further group-classification premise. -/
theorem LocalRelations.radiusThree_equiv_of_relations
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side)
    {M : Type*} [Group M] {x y z a b : M}
    (q : ThreeInvolutionFourCommutators.Relations x y z a b)
    (hgen : closure ({x,y,z} : Set M) = ⊤) :
    Nonempty ((d.labelBall v 3) ≃* M) := by
  obtain ⟨u, w, t, c, e, hrel, hfull⟩ := r.radiusThree_generators hr v hv
  obtain ⟨f, _⟩ := hrel.equiv_closure q
  exact ⟨(MulEquiv.subgroupCongr hfull.symm).trans
    (f.trans ((MulEquiv.subgroupCongr hgen).trans (Subgroup.topEquiv (G := M))))⟩

/-- The literal source radius-three label group is the concrete second
M₁₂ parabolic two-core. The model witness discharges the recognition premise. -/
theorem LocalRelations.radiusThree_equiv_secondCore
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side) :
    Nonempty ((d.labelBall v 3) ≃*
      Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition.SecondCore) :=
  r.radiusThree_equiv_of_relations hr v hv
    Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition.core_relations
    Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition.core_generation

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
