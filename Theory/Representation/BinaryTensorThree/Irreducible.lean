module
public import Theory.Representation.BinaryTensorThree
public import Theory.Representation.SpecialLinearNatural

/-!
# Irreducibility of the binary tensor base

Independent row and column transvections extract every matrix unit from a
nonzero invariant additive subgroup of the nine-dimensional tensor module.
Thus the two natural factors act irreducibly, without an enumeration of
subspaces or a semisimplicity hypothesis.

The original Chapter 10 tensor consumer uses this to identify its actual
nonzero homogeneous seed, local module and full module. This supplies the
module equality used at the start of the source centralizer argument.
Source: Aschbacher--Smith, 3.2.6(2) and H.4.4, printed pp.581,383.
-/

public noncomputable section
open scoped TensorProduct
namespace BinaryTensorThree
set_option backward.isDefEq.respectTransparency false

private theorem row_formula (g : Factor) (X : Space) (i : Fin 3) :
    baseAction (1,g) X i = g (X i) := by
  obtain ⟨x,rfl⟩ := coordinates.surjective X
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    change (0 : Natural) = g 0
    rw [map_zero]
  | tmul x y =>
    rw [baseAction_tmul]
    ext j
    simp only [coordinates_tmul]
    change x i * g y j = g (x i • y) j
    rw [map_smul]
    rfl
  | add x y hx hy =>
    simp only [map_add]
    change _ = g (coordinates x i + coordinates y i)
    rw [map_add]
    exact congrArg₂ (· + ·) hx hy

private theorem column_formula (g : Factor) (X : Space) (i j : Fin 3) :
    baseAction (g,1) X i j = g (fun k => X k j) i := by
  have h := congrArg (fun Y : Space => Y j i) (flip_baseAction (g,1) X)
  simp only [flip_apply,row_formula] at h
  exact h

private theorem transvection_apply {i j : Fin 3} (hij : i ≠ j) (v : Natural) :
    Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2)) v =
      v + Pi.single i (v j) := by
  change ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j 1).mulVec v = _
  simp only [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec_eq,one_mul]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

/-- Every nonzero additive subgroup invariant under both natural factors
contains all matrix units, so it is the whole tensor module. -/
theorem additive_invariant_eq_bot_or_top (S : AddSubgroup Space)
    (hS : ∀ g : Factor × Factor, ∀ X ∈ S, baseAction g X ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  have hrow {X : Space} (hX : X ∈ S) {i j : Fin 3} (hij : i ≠ j) :
      Pi.single i (X j) ∈ S := by
    let g : Factor := Matrix.SpecialLinearGroup.toLin'
      (Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2))
    have h := S.sub_mem (hS (g,1) X hX) hX
    have he : baseAction (g,1) X - X = Pi.single i (X j) := by
      ext k l
      rw [Pi.sub_apply,Pi.sub_apply,column_formula]
      change (Matrix.SpecialLinearGroup.toLin'
        (Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2)) (fun k => X k l)) k - X k l = _
      rw [transvection_apply]
      by_cases hk : k = i <;> simp [hk]
    rwa [he] at h
  have hrow' {X : Space} (hX : X ∈ S) (i j : Fin 3) : Pi.single i (X j) ∈ S := by
    by_cases hij : i = j
    · subst i
      obtain ⟨k,hkj⟩ : ∃ k : Fin 3, k ≠ j := by fin_cases j <;> decide
      simpa using hrow (hrow hX hkj) hkj.symm
    · exact hrow hX hij
  have hcol {X : Space} (hX : X ∈ S) {i j : Fin 3} (hij : i ≠ j) :
      (fun k => Pi.single i (X k j)) ∈ S := by
    let g : Factor := Matrix.SpecialLinearGroup.toLin'
      (Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2))
    have h := S.sub_mem (hS (1,g) X hX) hX
    have he : baseAction (1,g) X - X = (fun k => Pi.single i (X k j)) := by
      funext k
      change baseAction (1,g) X k - X k = _
      rw [row_formula]
      change Matrix.SpecialLinearGroup.toLin'
        (Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2)) (X k) - X k = _
      rw [transvection_apply,add_sub_cancel_left]
    rwa [he] at h
  have hcol' {X : Space} (hX : X ∈ S) (i j : Fin 3) :
      (fun k => Pi.single i (X k j)) ∈ S := by
    by_cases hij : i = j
    · subst i
      obtain ⟨k,hkj⟩ : ∃ k : Fin 3, k ≠ j := by fin_cases j <;> decide
      simpa using hcol (hcol hX hkj) hkj.symm
    · exact hcol hX hij
  have binary (a : ZMod 2) : a = 0 ∨ a = 1 := by fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
  by_cases hz : S = ⊥
  · exact Or.inl hz
  obtain ⟨X,hX,hX0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hz)
  have hXne : X ≠ 0 := hX0
  obtain ⟨i,j,hij⟩ : ∃ i j, X i j ≠ 0 := by
    by_contra! hh
    exact hXne (by ext i j; exact hh i j)
  have hunit (k l : Fin 3) : Pi.single k (Pi.single l (1 : ZMod 2)) ∈ S := by
    have h := hcol' (hrow' hX k i) l j
    have h1 : X i j = 1 := (binary (X i j)).resolve_left hij
    convert h using 1
    ext a b
    by_cases ha : a = k <;> simp [ha,h1]
  refine Or.inr (eq_top_iff.mpr (fun Y _ => ?_))
  have hsingle (i j : Fin 3) : Pi.single i (Pi.single j (Y i j)) ∈ S := by
    rcases binary (Y i j) with h | h
    · simp [h]
    · simpa [h] using hunit i j
  have hsum : Y = ∑ i : Fin 3, ∑ j : Fin 3, Pi.single i (Pi.single j (Y i j)) := by
    ext i j
    change Y i j = ∑ a : Fin 3, ∑ b : Fin 3, (Pi.single a (Pi.single b (Y a b)) : Space) i j
    simp [Pi.single_apply,ite_apply]
  rw [hsum]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => hsingle i j

end BinaryTensorThree
