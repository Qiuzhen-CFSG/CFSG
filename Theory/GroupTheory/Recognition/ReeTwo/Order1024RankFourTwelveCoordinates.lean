module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileData
public import Theory.SpecificGroups.ReeTwo.TailQuotientOrder16Nodes
public import Theory.Frattini.BinarySquares

/-!
# Coordinates for the twelfth residual Ree two subgroup

This subgroup consists exactly of the elements whose first two core coordinates
vanish. Its Frattini quotient has coordinates `(b3,b2,t mod 2,b5)`, with ordered
lifts `(root 3,root 2,rootOne,root 5)`. Squares and commutators supply the six
kernel generators; the core normal form proves that they generate the kernel.
The tail contributes the last quotient coordinate, so it is not the Frattini
subgroup.

Source: Shinoda (1975), (2.3), pp. 81–82, using the verified multiplication and
action in `ReeTwo.Core` and `ReeTwo.RootAction`.
-/

namespace ReeTwo.SylowModel.RankFourTwelve
set_option maxRecDepth 16384
private abbrev U := residualCandidate 12
private abbrev V := OrderProfileQuotient 4

private theorem root_mem (i : CoreRoot) (hi : 2 ≤ i.val) : root i ∈ U := by
  by_cases ht : 4 ≤ i.val
  · exact tailSubgroup_le_residualCandidate 12 (Subgroup.subset_closure ⟨i, ht, rfl⟩)
  · apply (show Subgroup.closure {root 3, root 2, rootOne} ≤ U from le_sup_right)
    apply Subgroup.subset_closure
    fin_cases i <;> simp_all

private theorem s_mem : rootOne ∈ U :=
  (show Subgroup.closure {root 3, root 2, rootOne} ≤ U from le_sup_right)
    (Subgroup.subset_closure (by simp))

/-- The first two core coordinates characterize the residual subgroup. -/
public theorem mem_candidate (g : SylowModel) : g ∈ residualCandidate 12 ↔ g.left.b0 = 0 ∧ g.left.b1 = 0 := by
  constructor
  · intro hg
    let H := (TailQuotient.Order16Nodes.node 19).comap TailQuotient.projection
    have hH : ∀ g : SylowModel, g ∈ H ↔ g.left.b0 = 0 ∧ g.left.b1 = 0 := by
      intro g
      exact (by decide +kernel : ∀ q : TailQuotient.Group,
        q ∈ TailQuotient.Order16Nodes.node 19 ↔ q.left.toAdd 0 = 0 ∧ q.left.toAdd 1 = 0)
        (TailQuotient.projection g)
    apply (hH g).mp
    apply (show U ≤ H from ?_) hg
    apply sup_le
    · intro x hx
      exact (hH x).mpr ⟨((mem_tailSubgroup x).mp hx).2.1,
        ((mem_tailSubgroup x).mp hx).2.2.1⟩
    · apply (Subgroup.closure_le _).mpr
      intro x hx
      change x ∈ ({root 3, root 2, rootOne} : Set SylowModel) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> exact (hH _).mpr (by decide +kernel)
  · rintro ⟨h0, h1⟩
    have hc : (SemidirectProduct.inl g.left : SylowModel) ∈ U := by
      have hn := congrArg (SemidirectProduct.inl : Core →* SylowModel) (Core.normal_form g.left)
      simp only [map_mul, map_pow, h0, h1, ZMod.val_zero, pow_zero, one_mul] at hn
      rw [← hn]
      exact U.mul_mem (U.mul_mem (U.mul_mem (U.mul_mem (U.mul_mem (U.mul_mem
        (U.mul_mem (U.pow_mem (root_mem 2 (by decide)) _) (U.pow_mem (root_mem 3 (by decide)) _))
        (U.pow_mem (root_mem 4 (by decide)) _)) (U.pow_mem (root_mem 5 (by decide)) _))
        (U.pow_mem (root_mem 6 (by decide)) _)) (U.pow_mem (root_mem 7 (by decide)) _))
        (U.pow_mem (root_mem 8 (by decide)) _)) (U.pow_mem (root_mem 9 (by decide)) _)
    have hr : (SemidirectProduct.inr g.right : SylowModel) ∈ U := by
      have he : ∀ t : FiveFour.Cyclic 4,
          (SemidirectProduct.inr t : SylowModel) = rootOne ^ ((-t.toAdd).val) := by decide +kernel
      rw [he]
      exact U.pow_mem s_mem _
    rw [← SemidirectProduct.inl_left_mul_inr_right g]
    exact U.mul_mem hc hr

private def core (v : Fin 8 → ZMod 2) : Core :=
  ⟨0,0,v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7⟩

private def view (x : Core) : Fin 5 → ZMod 2 := ![x.b0,x.b1,x.b2,x.b3,x.b5]
private def viewMul (x y : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 :=
  ![x 0 + y 0, x 1 + y 1, x 2 + y 2, x 3 + y 3,
    x 4 + x 2 * y 0 + x 3 * y 0 + x 1 * y 1 + y 4]
private theorem view_mul (x y : Core) : view (x*y) = viewMul (view x) (view y) := by
  funext i; fin_cases i <;> rfl
private def fixedView (f : MulAut Core) : Subgroup Core where
  carrier := {x | view (f x) = view x}
  one_mem' := by simp only [Set.mem_ofPred_eq, map_one]
  mul_mem' := by
    intro x y hx hy
    change view (f (x*y)) = view (x*y)
    change view (f x) = view x at hx
    change view (f y) = view y at hy
    rw [map_mul,view_mul,view_mul,hx,hy]
  inv_mem' := by
    intro x hx
    change view (f x) = view x at hx
    change view (f ((x*x)*x)) = view ((x*x)*x)
    simp only [map_mul,view_mul,hx]

set_option maxHeartbeats 2000000 in
private theorem action_coordinates (t : FiveFour.Cyclic 4) (v : Fin 8 → ZMod 2) :
    let c := Core.complementAction (SemidirectProduct.inr t) (core v)
    c.b0 = 0 ∧ c.b1 = 0 ∧ c.b2 = v 0 ∧ c.b3 = v 1 ∧ c.b5 = v 3 := by
  let K := fixedView (Core.complementAction (SemidirectProduct.inr t))
  have hr : ∀ i : CoreRoot, 2 ≤ i.val → Core.root i ∈ K :=
    (by decide +kernel : ∀ (t : FiveFour.Cyclic 4) (i : CoreRoot), 2 ≤ i.val →
      view (Core.complementAction (SemidirectProduct.inr t) (Core.root i)) = view (Core.root i)) t
  have hc : core v ∈ K := by
    rw [← Core.normal_form (core v)]
    simp only [core, ZMod.val_zero, pow_zero, one_mul]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
      (K.mul_mem (K.pow_mem (hr 2 (by decide)) _) (K.pow_mem (hr 3 (by decide)) _))
      (K.pow_mem (hr 4 (by decide)) _)) (K.pow_mem (hr 5 (by decide)) _))
      (K.pow_mem (hr 6 (by decide)) _)) (K.pow_mem (hr 7 (by decide)) _))
      (K.pow_mem (hr 8 (by decide)) _)) (K.pow_mem (hr 9 (by decide)) _)
  change view (Core.complementAction (SemidirectProduct.inr t) (core v)) = view (core v) at hc
  exact ⟨congrFun hc 0, congrFun hc 1, congrFun hc 2, congrFun hc 3, congrFun hc 4⟩

/-- Quotient coordinates in the ordered basis `(root 3, root 2, rootOne, root 5)`. -/
@[expose] public def coordinates : residualCandidate 12 →* OrderProfileQuotient 4 where
  toFun g := Multiplicative.ofAdd ![g.val.left.b3, g.val.left.b2,
    (parity g.val.right).toAdd, g.val.left.b5]
  map_one' := by decide +kernel
  map_mul' x y := by
    obtain ⟨h0,h1⟩ := (mem_candidate y.val).mp y.property
    have hy : y.val.left = core ![y.val.left.b2,y.val.left.b3,y.val.left.b4,y.val.left.b5,
        y.val.left.b6,y.val.left.b7,y.val.left.b8,y.val.left.b9] := by
      apply Core.ext <;> simp [core, h0, h1]
    have ha := action_coordinates x.val.right ![y.val.left.b2,y.val.left.b3,y.val.left.b4,
      y.val.left.b5,y.val.left.b6,y.val.left.b7,y.val.left.b8,y.val.left.b9]
    rw [← hy] at ha
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact congrArg (x.val.left.b3 + ·) ha.2.2.2.1
    · exact congrArg (x.val.left.b2 + ·) ha.2.2.1
    · exact congrArg Multiplicative.toAdd (map_mul parity x.val.right y.val.right)
    · change x.val.left.b5 + x.val.left.b2 *
        (Core.complementAction (SemidirectProduct.inr x.val.right) y.val.left).b0 +
        x.val.left.b3 * (Core.complementAction (SemidirectProduct.inr x.val.right) y.val.left).b0 +
        x.val.left.b1 * (Core.complementAction (SemidirectProduct.inr x.val.right) y.val.left).b1 +
        (Core.complementAction (SemidirectProduct.inr x.val.right) y.val.left).b5 =
        x.val.left.b5 + y.val.left.b5
      rw [ha.1, ha.2.1, ha.2.2.2.2]
      simp only [mul_zero, add_zero]
      rfl

private def representative (v : V) : U :=
  ⟨root 3 ^ (v.toAdd 0).val * root 2 ^ (v.toAdd 1).val *
    rootOne ^ (v.toAdd 2).val * root 5 ^ (v.toAdd 3).val,
    U.mul_mem (U.mul_mem (U.mul_mem (U.pow_mem (root_mem 3 (by decide)) _)
      (U.pow_mem (root_mem 2 (by decide)) _)) (U.pow_mem s_mem _))
      (U.pow_mem (root_mem 5 (by decide)) _)⟩

set_option maxHeartbeats 2000000 in
/-- The four prescribed lifts realize every binary quotient vector. -/
public theorem coordinates_surjective : Function.Surjective coordinates := by
  intro v
  exact ⟨representative v, (by decide +kernel : ∀ v, coordinates (representative v) = v) v⟩


private theorem two_group : IsPGroup 2 U :=
  (IsPGroup.of_card (n := 12) card).to_subgroup U

set_option maxHeartbeats 2000000 in
/-- Squares and commutators generate exactly the coordinate kernel. -/
public theorem kernel_eq_frattini : coordinates.ker = frattini (residualCandidate 12) := by
  let : Fact (IsPGroup 2 U) := ⟨two_group⟩
  apply le_antisymm
  · let W := (frattini U).map U.subtype
    have sq (x : SylowModel) (hx : x ∈ U) : x ^ 2 ∈ W :=
      Subgroup.mem_map_of_mem U.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x,hx⟩ : U))
    have comm (x y : SylowModel) (hx : x ∈ U) (hy : y ∈ U) : rightComm x y ∈ W := by
      apply Subgroup.mem_map_of_mem U.subtype (x := rightComm (⟨x,hx⟩ : U) ⟨y,hy⟩)
      apply commutator_le_frattini_of_isPGroup (p := 2)
      simpa only [commutatorElement_def, inv_inv, rightComm, commutator_def] using
        (Subgroup.commutator_mem_commutator
          (Subgroup.mem_top (⟨x,hx⟩ : U)⁻¹) (Subgroup.mem_top (⟨y,hy⟩ : U)⁻¹))
    have hs : rootOne ^ 2 ∈ W := sq _ s_mem
    have h9 : root 9 ∈ W := by
      rw [← show (root 2)^2 = root 9 from by decide +kernel]
      exact sq _ (root_mem 2 (by decide))
    have h8 : root 8 ∈ W := by
      rw [← show (root 3)^2 = root 8 from by decide +kernel]
      exact sq _ (root_mem 3 (by decide))
    have h7 : root 7 ∈ W := by
      rw [← show rightComm (root 3) (root 2) = root 7 from by decide +kernel]
      exact comm _ _ (root_mem 3 (by decide)) (root_mem 2 (by decide))
    have h4 : root 4 ∈ W := by
      rw [← show rightComm rootOne (root 3) = root 4 from by decide +kernel]
      exact comm _ _ s_mem (root_mem 3 (by decide))
    have h6 : root 6 ∈ W := by
      have h := comm _ _ s_mem (root_mem 5 (by decide))
      rw [show rightComm rootOne (root 5) = root 6 * root 8 * root 9 from by decide +kernel] at h
      exact (W.mul_mem_cancel_right h8).mp ((W.mul_mem_cancel_right h9).mp h)
    intro g hg
    have hz : coordinates g = 1 := hg
    have h3 : g.val.left.b3 = 0 := congrFun (congrArg Multiplicative.toAdd hz) 0
    have h2 : g.val.left.b2 = 0 := congrFun (congrArg Multiplicative.toAdd hz) 1
    have hp : parity g.val.right = 1 := congrArg Multiplicative.ofAdd
      (congrFun (congrArg Multiplicative.toAdd hz) 2)
    have h5 : g.val.left.b5 = 0 := congrFun (congrArg Multiplicative.toAdd hz) 3
    obtain ⟨h0,h1⟩ := (mem_candidate g.val).mp g.property
    have hc : (SemidirectProduct.inl g.val.left : SylowModel) ∈ W := by
      have hn := congrArg (SemidirectProduct.inl : Core →* SylowModel) (Core.normal_form g.val.left)
      simp only [map_mul, map_pow, h0,h1,h2,h3,h5, ZMod.val_zero,pow_zero,one_mul,mul_one] at hn
      rw [← hn]
      exact W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem
        (W.pow_mem h4 _) (W.pow_mem h6 _)) (W.pow_mem h7 _)) (W.pow_mem h8 _)) (W.pow_mem h9 _)
    have hr : (SemidirectProduct.inr g.val.right : SylowModel) ∈ W := by
      have he : ∀ t : FiveFour.Cyclic 4, parity t = 1 →
          (SemidirectProduct.inr t : SylowModel) = 1 ∨
          (SemidirectProduct.inr t : SylowModel) = rootOne ^ 2 := by decide +kernel
      rcases he _ hp with h | h
      · rw [h]; exact W.one_mem
      · rw [h]; exact hs
    have hw : g.val ∈ W := by
      rw [← SemidirectProduct.inl_left_mul_inr_right g.val]
      exact W.mul_mem hc hr
    obtain ⟨y, hy, he⟩ := hw
    exact (show y = g from Subtype.ext he) ▸ hy
  · rw [two_group.frattini_eq_closure_squares]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    change coordinates (x^2) = 1
    rw [map_pow]
    exact (by decide +kernel : ∀ v : V, v^2 = 1) _
end ReeTwo.SylowModel.RankFourTwelve
