module
public import Theory.Representation.BinaryTensorThree.PlaneFixed

/-!
# The two irreducible layers through a pure binary tensor

The point stabilizer preserves the five-space consisting of the first row
and first column. Modulo the fixed point, independent elementary matrices
and factor exchange generate all four remaining coordinates. Above the
five-space, independent elementary matrices generate the lower square.
These invariant-interval statements apply directly to original subgroups.

Source: Aschbacher--Smith H.4.9(2), used in 8.3.12, printed pp.384,726.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup
open scoped TensorProduct
namespace BinaryTensorThree.PointFlag
open Matrix.PSL3Two

def line : Submodule (ZMod 2) Space where
  carrier := {X | ∀ i j, i ≠ 0 ∨ j ≠ 0 → X i j = 0}
  zero_mem' := by simp
  add_mem' := by intro X Y hX hY i j h; simp [hX i j h,hY i j h]
  smul_mem' := by intro c X hX i j h; simp [hX i j h]

def five : Submodule (ZMod 2) Space where
  carrier := {X | ∀ i j, i ≠ 0 → j ≠ 0 → X i j = 0}
  zero_mem' := by simp
  add_mem' := by intro X Y hX hY i j hi hj; simp [hX i j hi hj,hY i j hi hj]
  smul_mem' := by intro c X hX i j hi hj; simp [hX i j hi hj]

theorem line_le_five : line ≤ five := fun _ h i j hi _ => h i j (Or.inl hi)

theorem mem_line_iff (X : Space) : X ∈ line ↔ X = 0 ∨ X = point := by
  have hp (i j : Fin 3) : point i j = if i = 0 ∧ j = 0 then 1 else 0 := by
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [point,coordinates_tmul,basisVector,hi,hj]
  constructor
  · intro h
    have he : X = X 0 0 • point := by
      ext i j
      by_cases hi : i = 0 <;> by_cases hj : j = 0
      · subst i; subst j; simp [hp]
      all_goals
        have hz := h i j (by tauto)
        simpa [hp,hi,hj] using hz
    have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hb (X 0 0) with hz | ho
    · exact Or.inl (by simpa [hz] using he)
    · exact Or.inr (by simpa [ho] using he)
  · rintro (rfl | rfl)
    · exact line.zero_mem
    · intro i j h
      rw [hp,if_neg]
      tauto

private theorem matrix_action (a b : SL) (X : Space) :
    baseAction (Matrix.SpecialLinearGroup.toLin' a,Matrix.SpecialLinearGroup.toLin' b) X =
      a.val * X * b.val.transpose := by
  obtain ⟨x,rfl⟩ := coordinates.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [baseAction_tmul]
    ext i j
    change (a.val.mulVec x) i * (b.val.mulVec y) j = _
    simp only [Matrix.mul_apply,Matrix.transpose_apply,coordinates_tmul,
      Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  | add x y hx hy => simp [map_add,Matrix.mul_add,Matrix.add_mul,hx,hy]

private theorem base_preserves_five (a b : SL)
    (ha : a ∈ pointParabolicSL) (hb : b ∈ pointParabolicSL)
    {X : Space} (hX : X ∈ five) :
    baseAction (Matrix.SpecialLinearGroup.toLin' a,Matrix.SpecialLinearGroup.toLin' b) X ∈ five := by
  obtain ⟨ha1,ha2⟩ := (mem_pointParabolicSL_iff a).mp ha
  obtain ⟨hb1,hb2⟩ := (mem_pointParabolicSL_iff b).mp hb
  rw [matrix_action]
  intro i j hi hj
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_three,
      hX 1 1 (by decide) (by decide),hX 1 2 (by decide) (by decide),
      hX 2 1 (by decide) (by decide),hX 2 2 (by decide) (by decide)]

/-- The literal point stabilizer preserves the five-space. -/
theorem preserves_five (g : BinaryTensorThree.Group) (hg : action g point = point)
    {X : Space} (hX : X ∈ five) : action g X ∈ five := by
  obtain ⟨a,ha⟩ := PointParabolic.actorEquiv.surjective g
  have he : PointParabolic.tensorHom a = g := by
    rwa [PointParabolic.actorEquiv_apply] at ha
  have hp := (PointParabolic.fixes_point_iff a).mp (he ▸ hg)
  rw [←he,PointParabolic.tensorHom_eq_wreathHom]
  change action (wreathMap _) X ∈ five
  unfold wreathMap
  split
  · exact base_preserves_five _ _ (hp 1) (hp _) hX
  · rw [map_mul,Module.End.mul_apply,action_swap,action_baseEmbedding]
    exact base_preserves_five _ _ (hp 1) (hp _) (fun i j hi hj => hX j i hj hi)

private theorem flip_stable (S : AddSubgroup Space)
    (hS : ∀ g : BinaryTensorThree.Group, action g point = point →
      ∀ X ∈ S, action g X ∈ S) {X : Space} (hX : X ∈ S) : flip X ∈ S :=
  hS swap (by ext i j; simp [point,coordinates_tmul,mul_comm]) X hX

private theorem row_extract (S : AddSubgroup Space)
    (hS : ∀ g : BinaryTensorThree.Group, action g point = point →
      ∀ X ∈ S, action g X ∈ S) {X : Space} (hX : X ∈ S)
    {i j : Fin 3} (hij : i ≠ j) (hj : j ≠ 0) : Pi.single i (X j) ∈ S := by
  let t := Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2)
  let g := baseEmbedding (Matrix.SpecialLinearGroup.toLin' t,1)
  have hf (Y : Space) : action g Y - Y = Pi.single i (Y j) := by
    change baseAction (Matrix.SpecialLinearGroup.toLin' t,1) Y - Y = _
    rw [show (1 : Factor) = Matrix.SpecialLinearGroup.toLin' (1 : SL) from (map_one _).symm]
    rw [matrix_action]
    change ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j 1) * Y * (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose - Y = _
    simp only [Matrix.transpose_one,Matrix.mul_one,Matrix.add_mul,Matrix.one_mul,add_sub_cancel_left]
    ext k l
    by_cases hk : k = i
    · subst k; simp [Matrix.single_mul_apply_same]
    · rw [Matrix.single_mul_apply_of_ne (1 : ZMod 2) i j k l hk Y]
      simp [hk]
  have hp : action g point = point := by
    apply sub_eq_zero.mp
    rw [hf]
    have hz : point j = 0 := by ext k; simp [point,coordinates_tmul,basisVector,hj]
    simp [hz]
  have hh := S.sub_mem (hS g hp X hX) hX
  rwa [hf] at hh

private theorem row_extract_nonzero (S : AddSubgroup Space)
    (hS : ∀ g : BinaryTensorThree.Group, action g point = point →
      ∀ X ∈ S, action g X ∈ S) {X : Space} (hX : X ∈ S)
    (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) : Pi.single i (X j) ∈ S := by
  by_cases hij : i = j
  · subst i
    obtain ⟨k,hk,hkj⟩ : ∃ k : Fin 3, k ≠ 0 ∧ k ≠ j := by fin_cases j <;> decide
    simpa using row_extract S hS (row_extract S hS hX hkj hj) hkj.symm hk
  · exact row_extract S hS hX hij hj

private theorem col_extract_nonzero (S : AddSubgroup Space)
    (hS : ∀ g : BinaryTensorThree.Group, action g point = point →
      ∀ X ∈ S, action g X ∈ S) {X : Space} (hX : X ∈ S)
    (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
    (fun k => Pi.single i (X k j)) ∈ S := by
  have he : flip (Pi.single i (flip X j)) = (fun k => Pi.single i (X k j)) := by
    ext k l
    simp [flip_apply,Pi.single_apply,ite_apply]
  rw [←he]
  exact flip_stable S hS (row_extract_nonzero S hS (flip_stable S hS hX) i j hi hj)

private theorem sum_units (X : Space) :
    X = ∑ i : Fin 3, ∑ j : Fin 3, Pi.single i (Pi.single j (X i j)) := by
  ext i j
  change X i j = ∑ a : Fin 3, ∑ b : Fin 3, (Pi.single a (Pi.single b (X a b)) : Space) i j
  simp [Pi.single_apply,ite_apply]

private theorem binary (a : ZMod 2) : a = 0 ∨ a = 1 := by fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The point stabilizer is irreducible on the five-space modulo its fixed line. -/
theorem lower_irreducible (S : AddSubgroup Space) (hline : line.toAddSubgroup ≤ S)
    (hfive : S ≤ five.toAddSubgroup)
    (hS : ∀ g : BinaryTensorThree.Group, action g point = point →
      ∀ X ∈ S, action g X ∈ S) : S = line.toAddSubgroup ∨ S = five.toAddSubgroup := by
  by_cases hl : S ≤ line.toAddSubgroup
  · exact Or.inl (le_antisymm hl hline)
  obtain ⟨X,hX,hXl⟩ := SetLike.not_le_iff_exists.mp hl
  have hx5 := hfive hX
  obtain ⟨Y,hY,hY5,j,hj,hy⟩ : ∃ Y ∈ S, Y ∈ five ∧ ∃ j : Fin 3, j ≠ 0 ∧ Y j 0 ≠ 0 := by
    have hn : ∃ i j, (i ≠ 0 ∨ j ≠ 0) ∧ X i j ≠ 0 := by
      change ¬ (∀ i j, i ≠ 0 ∨ j ≠ 0 → X i j = 0) at hXl
      push Not at hXl
      exact hXl
    obtain ⟨i,j,hh,hne⟩ := hn
    by_cases hi : i = 0
    · subst i
      exact ⟨flip X,flip_stable S hS hX,(fun i j hi hj => hx5 j i hj hi),j,
        hh.resolve_left (not_not.mpr rfl),hne⟩
    · have hj0 : j = 0 := by by_contra hj; exact hne (hx5 i j hi hj)
      subst j
      exact ⟨X,hX,hx5,i,hi,hne⟩
  have hone : Y j 0 = 1 := (binary _).resolve_left hy
  have hleft (i : Fin 3) (hi : i ≠ 0) : Pi.single i (Pi.single 0 (1 : ZMod 2)) ∈ S := by
    have he : Y j = Pi.single 0 (1 : ZMod 2) := by
      ext k
      by_cases hk : k = 0
      · subst k; simpa using hone
      · simp [hk,hY5 j k hj hk]
    simpa only [he] using row_extract_nonzero S hS hY i j hi hj
  have hright (i : Fin 3) (hi : i ≠ 0) : Pi.single 0 (Pi.single i (1 : ZMod 2)) ∈ S := by
    have he : flip (Pi.single i (Pi.single 0 (1 : ZMod 2))) =
        Pi.single 0 (Pi.single i (1 : ZMod 2)) := by
      ext k l
      by_cases hk : k = 0 <;> by_cases hl : l = i <;> simp [flip_apply,hk,hl]
    rw [←he]
    exact flip_stable S hS (hleft i hi)
  refine Or.inr (le_antisymm hfive ?_)
  intro W hW
  rw [sum_units W]
  apply S.sum_mem
  intro i _
  apply S.sum_mem
  intro j _
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst i; subst j
    apply hline
    intro k l h
    rcases h with h | h <;> simp [Pi.single_apply,ite_apply,h]
  · subst i
    rcases binary (W 0 j) with hz | ho
    · simp [hz]
    · simpa only [ho] using hright j hj
  · subst j
    rcases binary (W i 0) with hz | ho
    · simp [hz]
    · simpa only [ho] using hleft i hi
  · simp [hW i j hi hj]

/-- The top four-dimensional quotient is irreducible for the same literal stabilizer. -/
theorem upper_irreducible (S : AddSubgroup Space) (hfive : five.toAddSubgroup ≤ S)
    (hS : ∀ g : BinaryTensorThree.Group, action g point = point →
      ∀ X ∈ S, action g X ∈ S) : S = five.toAddSubgroup ∨ S = ⊤ := by
  by_cases hl : S ≤ five.toAddSubgroup
  · exact Or.inl (le_antisymm hl hfive)
  obtain ⟨X,hX,hXf⟩ := SetLike.not_le_iff_exists.mp hl
  obtain ⟨i,j,hi,hj,hij⟩ : ∃ i j, i ≠ 0 ∧ j ≠ 0 ∧ X i j ≠ 0 := by
    change ¬ (∀ i j, i ≠ 0 → j ≠ 0 → X i j = 0) at hXf
    push Not at hXf
    exact hXf
  have hu (k l : Fin 3) (hk : k ≠ 0) (hl : l ≠ 0) :
      Pi.single k (Pi.single l (1 : ZMod 2)) ∈ S := by
    have h := col_extract_nonzero S hS (row_extract_nonzero S hS hX k i hk hi) l j hl hj
    have ho : X i j = 1 := (binary _).resolve_left hij
    convert h using 1
    ext a b
    by_cases ha : a = k <;> simp [ha,ho]
  refine Or.inr (eq_top_iff.mpr (fun W _ => ?_))
  rw [sum_units W]
  apply S.sum_mem
  intro k _
  apply S.sum_mem
  intro l _
  by_cases hk : k = 0
  · subst k
    apply hfive
    intro i j hi hj
    simp [hi]
  by_cases hl : l = 0
  · subst l
    apply hfive
    intro i j hi hj
    simp [Pi.single_apply,ite_apply,hj]
  rcases binary (W k l) with hz | ho
  · simp [hz]
  · simpa only [ho] using hu k l hk hl


/-- The five literal free coordinates of the point flag. -/
def fiveEquiv : five ≃ₗ[ZMod 2] ((ZMod 2) × (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) where
  toFun X := (X.val 0 0,(fun i => X.val i.succ 0),fun j => X.val 0 j.succ)
  invFun a := ⟨!![a.1,a.2.2 0,a.2.2 1;a.2.1 0,0,0;a.2.1 1,0,0],by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp_all⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X.property 1 1 (by decide) (by decide),X.property 1 2 (by decide) (by decide),
        X.property 2 1 (by decide) (by decide),X.property 2 2 (by decide) (by decide)]
  right_inv a := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    all_goals ext i; fin_cases i <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_five : Module.finrank (ZMod 2) five = 5 := by
  rw [fiveEquiv.finrank_eq,Module.finrank_prod,Module.finrank_prod]
  norm_num

end BinaryTensorThree.PointFlag
