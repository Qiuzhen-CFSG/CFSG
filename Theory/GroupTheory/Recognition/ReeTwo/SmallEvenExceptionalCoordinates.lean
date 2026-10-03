module
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates
public import Theory.SpecificGroups.ReeTwo.SylowTailQuotient
/-!
# Coordinates for the exceptional small even Ree two subgroup

The specified nine root words generate exactly the elements with zero first
and second core coordinates and even cyclic-four coordinate. Nine independent
binary coordinates parametrize this subgroup. Its square map is a quadratic
map into the last three roots. Every value with zero root-7 coordinate has
80 square roots; each other value in these three roots has 48.

The multiplication is the verified Shinoda (1975), (2.3), pp. 81–82 model.
All finite certificates below are checked by the Lean kernel.
-/

@[expose] public section
namespace ReeTwo.SylowModel
namespace SmallEvenExceptional
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
def qmember (q : TailQuotient.Group) : Prop :=
  q.left.toAdd 0 = 0 ∧ q.left.toAdd 1 = 0 ∧ parity q.right = 1
instance (q : TailQuotient.Group) : Decidable (qmember q) := by unfold qmember; infer_instance
theorem qclosed : qmember 1 ∧
    (∀ a b, qmember a → qmember b → qmember (a * b)) ∧
    (∀ a, qmember a → qmember a⁻¹) := by decide +kernel
def qnode : Subgroup TailQuotient.Group where
  carrier := qmember
  one_mem' := qclosed.1
  mul_mem' := qclosed.2.1 _ _
  inv_mem' := qclosed.2.2 _
def coordinateSubgroup : Subgroup SylowModel := qnode.comap TailQuotient.projection
theorem mem_coordinateSubgroup (x : SylowModel) : x ∈ coordinateSubgroup ↔
    x.left.b0 = 0 ∧ x.left.b1 = 0 ∧ parity x.right = 1 := Iff.rfl
instance (x : SylowModel) : Decidable (x ∈ coordinateSubgroup) := by
  change Decidable (qmember (TailQuotient.projection x)); infer_instance
def word (v : Fin 9 → ZMod 2) : SylowModel :=
  root 2 ^ (v 1).val * root 3 ^ (v 2).val * root 4 ^ (v 3).val *
  root 5 ^ (v 4).val * root 6 ^ (v 5).val * root 7 ^ (v 6).val *
  root 8 ^ (v 7).val * root 9 ^ (v 8).val * (rootOne ^ 2) ^ (v 0).val
theorem base_mem : rootOne ^ 2 ∈ smallEvenExceptional ∧
    ∀ i : CoreRoot, 2 ≤ i.val → root i ∈ smallEvenExceptional := by
  let U := smallEvenExceptional
  have gen : ∀ x ∈ ({root 3, rootOne ^ 2, root 4 * root 7 * root 8,
      root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9,
      root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9,
      root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel), x ∈ U := by
    intro x hx
    apply Subgroup.subset_closure
    exact hx
  have h9 : root 9 ∈ U := gen _ (by simp)
  have h8 : root 8 ∈ U := (U.mul_mem_cancel_right h9).mp (gen _ (by simp))
  have h7 : root 7 ∈ U := (U.mul_mem_cancel_right h9).mp (gen _ (by simp))
  have h6 : root 6 ∈ U := (U.mul_mem_cancel_right h7).mp
    ((U.mul_mem_cancel_right h8).mp ((U.mul_mem_cancel_right h9).mp (gen _ (by simp))))
  have h4 : root 4 ∈ U := (U.mul_mem_cancel_right h7).mp
    ((U.mul_mem_cancel_right h8).mp (gen _ (by simp)))
  have h3 : root 3 ∈ U := gen _ (by simp)
  have h2 : root 2 ∈ U := (U.mul_mem_cancel_right h3).mp
    ((U.mul_mem_cancel_right h4).mp ((U.mul_mem_cancel_right h9).mp (gen _ (by simp))))
  have h5 : root 5 ∈ U := (U.mul_mem_cancel_left (U.mul_mem (U.mul_mem h2 h3) h4)).mp
    ((U.mul_mem_cancel_right h6).mp ((U.mul_mem_cancel_right h7).mp
      ((U.mul_mem_cancel_right h9).mp (gen _ (by simp)))))
  refine ⟨gen _ (by simp), ?_⟩
  intro i hi
  fin_cases i <;> norm_num at hi
  all_goals first | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7 | exact h8 | exact h9

def coords (x : SylowModel) : Fin 9 → ZMod 2 :=
  ![((x.right.toAdd.val / 2 : ℕ) : ZMod 2), x.left.b2, x.left.b3, x.left.b4,
    x.left.b5, x.left.b6, x.left.b7, x.left.b8, x.left.b9]

theorem word_coords (x : SylowModel) (hx : x ∈ coordinateSubgroup) :
    word (coords x) = x := by
  obtain ⟨h0,h1,hr⟩ := (mem_coordinateSubgroup x).mp hx
  have hc := congrArg (SemidirectProduct.inl : Core →* SylowModel) (Core.normal_form x.left)
  simp only [map_mul, map_pow, h0, h1, ZMod.val_zero, pow_zero, one_mul] at hc
  have ht : ∀ t : FiveFour.Cyclic 4, parity t = 1 →
      (rootOne ^ 2) ^ (((t.toAdd.val / 2 : ℕ) : ZMod 2).val) =
      (SemidirectProduct.inr t : SylowModel) := by decide +kernel
  change _ * (rootOne ^ 2) ^ _ = x
  dsimp only [coords, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons]
  rw [ht x.right hr]
  change (root 2 ^ x.left.b2.val * root 3 ^ x.left.b3.val * root 4 ^ x.left.b4.val *
    root 5 ^ x.left.b5.val * root 6 ^ x.left.b6.val * root 7 ^ x.left.b7.val *
    root 8 ^ x.left.b8.val * root 9 ^ x.left.b9.val) * SemidirectProduct.inr x.right = x
  rw [show root 2 ^ x.left.b2.val * root 3 ^ x.left.b3.val * root 4 ^ x.left.b4.val *
    root 5 ^ x.left.b5.val * root 6 ^ x.left.b6.val * root 7 ^ x.left.b7.val *
    root 8 ^ x.left.b8.val * root 9 ^ x.left.b9.val =
    SemidirectProduct.inl x.left from hc]
  exact SemidirectProduct.inl_left_mul_inr_right x

theorem word_mem (v : Fin 9 → ZMod 2) : word v ∈ smallEvenExceptional := by
  unfold word
  repeat apply Subgroup.mul_mem
  all_goals apply Subgroup.pow_mem
  all_goals first | exact base_mem.1 | exact base_mem.2 _ (by decide)

theorem subgroup_eq : coordinateSubgroup = smallEvenExceptional := by
  apply le_antisymm
  · intro x hx
    rw [← word_coords x hx]
    exact word_mem _
  · apply (Subgroup.closure_le _).mpr
    change {root 3, rootOne ^ 2, root 4 * root 7 * root 8,
      root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9,
      root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9,
      root 7 * root 9, root 8 * root 9, root 9} ⊆ (coordinateSubgroup : Set SylowModel)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> change _ ∈ coordinateSubgroup <;> decide +kernel

abbrev V := Fin 9 → ZMod 2
def element (v : V) : SylowModel :=
  ⟨⟨0,0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8⟩, Multiplicative.ofAdd (2 * (v 0).val : ZMod 4)⟩
theorem element_mem (v : V) : element v ∈ coordinateSubgroup := by
  refine ⟨rfl,rfl,?_⟩
  exact (by decide +kernel : ∀ a : ZMod 2, parity (Multiplicative.ofAdd (2 * a.val : ZMod 4)) = 1) (v 0)
def equiv : coordinateSubgroup ≃ V where
  toFun x := coords x
  invFun v := ⟨element v,element_mem v⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨h0,h1,hr⟩ := (mem_coordinateSubgroup x).mp x.property
    apply SemidirectProduct.ext
    · apply Core.ext <;> first | rfl | exact h0.symm | exact h1.symm
    · exact (by decide +kernel : ∀ t : FiveFour.Cyclic 4, parity t = 1 →
        Multiplicative.ofAdd (2 * (((t.toAdd.val / 2 : ℕ) : ZMod 2).val) : ZMod 4) = t) x.val.right hr
  right_inv v := by
    funext i
    fin_cases i <;> first | rfl | exact (by decide +kernel : ∀ a : ZMod 2,
      (((2 * a.val : ZMod 4).val / 2 : ℕ) : ZMod 2) = a) (v 0)
def last (w : Fin 3 → ZMod 2) : SylowModel :=
  ⟨⟨0,0,0,0,0,0,0,w 0,w 1,w 2⟩,1⟩
def sq (v : V) : Fin 3 → ZMod 2 :=
  ![v 1 * v 2 + v 0 * v 4,
    v 2 + v 1 * v 3 + v 0 * v 4 + v 0 * v 5,
    v 1 + v 0 * v 4 + v 2 * v 5 + v 3 * v 4]
theorem square_formula : ∀ v : V, element v ^ 2 = last (sq v) := by decide +kernel
theorem sq_count : ∀ w : Fin 3 → ZMod 2,
    Fintype.card {v : V // sq v = w} = if w 0 = 0 then 80 else 48 := by decide +kernel

end SmallEvenExceptional
end ReeTwo.SylowModel
