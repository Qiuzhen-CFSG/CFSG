module
public import Theory.SpecificGroups.HeisenbergFour.CubicIncidence.Axes
public import Theory.SpecificGroups.SL2.BinaryTetrahedralHom
public import Theory.SpecificGroups.SL2.BinaryTetrahedralQuotient

/-!
# Opposite-axis joins are binary tetrahedral

For cubic generators t and v on opposite axes, put a = v t⁻¹ and
b = t a t⁻¹ a⁻¹. The quaternion relations and the prescribed cubic action
construct a homomorphism from Q₈ ⋊ C₃. Every nontrivial normal subgroup
contains the central involution, whose image is nontrivial. Thus the map is
injective, and its normal forms show that its range is exactly the join.
The existing binary tetrahedral matrix equivalence then identifies this
literal join with SL₂(3).

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.6(1), p.264.
-/

@[expose] public section
namespace HeisenbergFour.CubicIncidence
open Subgroup GLS3.Chapter5.SchurPresentation

private instance binaryFintype : Fintype BinaryTetrahedral :=
  Fintype.ofEquiv (QuaternionGroup 2 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

private def first (i j : Four × Four) : CoordinateModel := gen j * (gen i)⁻¹
private def second (i j : Four × Four) : CoordinateModel :=
  gen i * first i j * (gen i)⁻¹ * (first i j)⁻¹

private theorem relations : ∀ i j : Four × Four, Cross i j →
    (first i j) ^ 4 = 1 ∧ (second i j) ^ 2 = (first i j) ^ 2 ∧
    second i j * first i j = (first i j)⁻¹ * second i j ∧
    gen i * first i j * (gen i)⁻¹ = second i j * first i j ∧
    gen i * second i j * (gen i)⁻¹ = (first i j)⁻¹ ∧
    (first i j) ^ 2 ≠ 1 := by decide +kernel

private def word (i j : Four × Four) (x : BinaryTetrahedral) : CoordinateModel :=
  (match x.left with
    | .a n => first i j ^ n.val
    | .xa n => second i j * first i j ^ n.val) *
  gen i ^ (Multiplicative.toAdd x.right).val

/-- Every nontrivial kernel meets the central involution. -/
private theorem injective_of_central_involution {E : Type*} [Group E]
    (f : BinaryTetrahedral →* E) (h : f (binaryI ^ 2) ≠ 1) : Function.Injective f := by
  have cover : ∀ x : BinaryTetrahedral,
      x = 1 ∨ x = binaryI ^ 2 ∨ x ^ 2 = binaryI ^ 2 ∨
      (binaryI * x * binaryI⁻¹ * x⁻¹) ^ 2 = binaryI ^ 2 := by decide +kernel
  apply f.ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  change f x = 1 at hx
  rcases cover x with he | he | he | he
  · exact he
  · exact False.elim (h (he ▸ hx))
  · apply False.elim
    apply h
    rw [← he, map_pow, hx, one_pow]
  · apply False.elim
    apply h
    rw [← he]
    simp only [map_pow, map_mul, map_inv, hx, mul_one, mul_inv_cancel, inv_one, one_pow]

private theorem hom_word (i j : Four × Four) (f : BinaryTetrahedral →* CoordinateModel)
    (hI : f binaryI = first i j) (hJ : f binaryJ = second i j)
    (hT : f binaryT = gen i) (x : BinaryTetrahedral) : f x = word i j x := by
  have hl (q : QuaternionGroup 2) : f (SemidirectProduct.inl q) =
      match q with
      | .a n => first i j ^ n.val
      | .xa n => second i j * first i j ^ n.val := by
    rcases q with n | n
    · rw [← ZMod.natCast_zmod_val n, ← QuaternionGroup.a_one_pow,
        map_pow, map_pow, hI]
      simp
    · have hq : QuaternionGroup.xa n = QuaternionGroup.xa 0 * QuaternionGroup.a n := by
        simp [QuaternionGroup.xa_mul_a]
      rw [hq, map_mul, map_mul, hJ]
      rw [← ZMod.natCast_zmod_val n, ← QuaternionGroup.a_one_pow,
        map_pow, map_pow, hI]
      simp
  have ht (k : Multiplicative (ZMod 3)) : f (SemidirectProduct.inr k) =
      gen i ^ (Multiplicative.toAdd k).val := by
    have he : (SemidirectProduct.inr k : BinaryTetrahedral) =
        binaryT ^ (Multiplicative.toAdd k).val := by
      change ZMod 3 at k
      fin_cases k <;> decide +kernel
    rw [he, map_pow, hT]
  calc
    f x = f (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right) :=
      congrArg f (SemidirectProduct.inl_left_mul_inr_right x).symm
    _ = word i j x := by rw [map_mul, hl, ht]; rfl

/-- An actual matrix-group equivalence for every opposite-axis pair. -/
theorem cross_join_equiv (i j : Four × Four) (hc : Cross i j) :
    Nonempty (↥(C i ⊔ C j) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨ha, hb, hba, htA, htB, hne⟩ := relations i j hc
  obtain ⟨f, hI, hJ, hT⟩ := exists_binaryTetrahedral_hom
    (first i j) (second i j) (gen i) ha hb hba
    (by rw [← gen_order i]; exact pow_orderOf_eq_one _) htA htB
  have hf : Function.Injective f := injective_of_central_involution f (by
    rw [map_pow, hI]
    exact hne)
  have hr : f.range = C i ⊔ C j := by
    apply le_antisymm
    · have hi : gen i ∈ C i ⊔ C j  := (show C i ≤ C i ⊔ C j from le_sup_left) (mem_zpowers _)
      have hj : gen j ∈ C i ⊔ C j  := (show C j ≤ C i ⊔ C j from le_sup_right) (mem_zpowers _)
      have ha' : first i j ∈ C i ⊔ C j := mul_mem hj (inv_mem hi)
      have hb' : second i j ∈ C i ⊔ C j :=
        mul_mem (mul_mem (mul_mem hi ha') (inv_mem hi)) (inv_mem ha')
      rintro _ ⟨x, rfl⟩
      rw [hom_word i j f hI hJ hT]
      unfold word
      cases x.left with
      | a n => exact mul_mem (pow_mem ha' _) (pow_mem hi _)
      | xa n => exact mul_mem (mul_mem hb' (pow_mem ha' _)) (pow_mem hi _)
    · apply sup_le
      · exact zpowers_le.mpr ⟨binaryT, hT⟩
      · apply zpowers_le.mpr
        refine ⟨binaryI * binaryT, ?_⟩
        rw [map_mul, hI, hT]
        simp [first, mul_assoc]
  exact ⟨(MulEquiv.subgroupCongr hr.symm).trans
    ((MonoidHom.ofInjective hf).symm.trans binaryTetrahedralEquivSL)⟩

end HeisenbergFour.CubicIncidence
