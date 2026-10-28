module

public import Theory.SpecificGroups.HigherLinear.SylowPointwiseInner.Actions
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.CharP.Lemmas

/-!
# The positive root subgroup in characteristic two is a two-group

Strictly upper triangular matrices of size d have d-th power zero. The
characteristic-two power identity therefore gives exponent dividing 2^d
for upper unitriangular matrices. The positive transvections lie in this
subgroup of SL, and passage through the literal quotient SL/Z(SL) preserves
the two-group property.

Only containment in a Sylow subgroup will be needed by the fixer argument.
No group-order formula, root-generation theorem for the full unitriangular
group, or maximality assertion is used.

Source: the type-A unipotent groups in GLS III §2.3 and §2.7; used for
Aschbacher–Smith B.1.13, printed p.74.
-/

public section
open scoped MatrixGroups
open Matrix
namespace Matrix.HigherLinear.SylowPointwiseInner
variable {d : ℕ} {F : Type*} [Field F]

private theorem strictly_upper_pow_entry (M : Matrix (Fin d) (Fin d) F)
    (hM : ∀ i j, j ≤ i → M i j = 0) (k : ℕ) :
    ∀ i j : Fin d, j.val < i.val + k → (M ^ k) i j = 0 := by
  induction k with
  | zero =>
    intro i j hij
    have hne : i ≠ j := by intro he; subst j; omega
    simp [hne]
  | succ k ih =>
    intro i j hij
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l ≤ i
    · rw [hM i l hl, zero_mul]
    · rw [ih l j (by have := lt_of_not_ge hl; omega), mul_zero]

private theorem strictly_upper_nilpotent (M : Matrix (Fin d) (Fin d) F)
    (hM : ∀ i j, j ≤ i → M i j = 0) : M ^ d = 0 := by
  ext i j
  exact strictly_upper_pow_entry M hM d i j (by have := j.isLt; omega)

private def IsUnitriangular (M : Matrix (Fin d) (Fin d) F) : Prop :=
  M.IsUpperTriangular ∧ ∀ i, M i i = 1

private theorem unitriangular_one : IsUnitriangular (1 : Matrix (Fin d) (Fin d) F) :=
  ⟨Matrix.blockTriangular_one, by simp⟩

private theorem unitriangular_mul {A B : Matrix (Fin d) (Fin d) F}
    (hA : IsUnitriangular A) (hB : IsUnitriangular B) : IsUnitriangular (A * B) := by
  refine ⟨hA.1.mul hB.1, ?_⟩
  intro i
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hA.2, hB.2, one_mul]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [hA.1 hj, zero_mul]
    · rw [hB.1 hj, mul_zero]
  · simp

private theorem unitriangular_pow {A : Matrix (Fin d) (Fin d) F}
    (hA : IsUnitriangular A) (k : ℕ) : IsUnitriangular (A ^ k) := by
  induction k with
  | zero => simpa using unitriangular_one (d := d) (F := F)
  | succ k ih => simpa only [pow_succ] using unitriangular_mul ih hA

variable [NeZero d]

private theorem unitriangular_two_pow [CharP F 2]
    {A : Matrix (Fin d) (Fin d) F} (hA : IsUnitriangular A) : A ^ (2 ^ d) = 1 := by
  have hstrict : ∀ i j, j ≤ i → (A - 1) i j = 0 := by
    intro i j hij
    rcases eq_or_lt_of_le hij with he | he
    · subst j
      simp [hA.2]
    · simp [hA.1 he, ne_of_gt he]
  have hnil : (A - 1) ^ (2 ^ d) = 0 :=
    pow_eq_zero_of_le (Nat.le_of_lt (Nat.lt_two_pow_self))
      (strictly_upper_nilpotent (A - 1) hstrict)
  let : CharP (Matrix (Fin d) (Fin d) F) 2 := ⟨fun k => by
      simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
        CharP.cast_eq_zero_iff F 2 k, forall_const]⟩
  have hp := add_pow_char_pow_of_commute 2 d (Commute.one_right (A - 1))
  simpa only [sub_add_cancel, hnil, one_pow, zero_add] using hp

private def upperSpecial [CharP F 2] : Subgroup SL(d,F) where
  carrier := {g | IsUnitriangular g.val}
  one_mem' := unitriangular_one
  mul_mem' := fun hx hy => unitriangular_mul hx hy
  inv_mem' := by
    intro g hg
    have hp : g ^ (2 ^ d) = 1 := Subtype.ext (by
      simpa only [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one] using unitriangular_two_pow hg)
    have he : g ^ (2 ^ d - 1) = g⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ 2 ^ d from Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))), hp]
    change IsUnitriangular (g⁻¹).val
    rw [← he]
    simpa only [SpecialLinearGroup.coe_pow] using unitriangular_pow hg (2 ^ d - 1)

private theorem upperSpecial_isPGroup [CharP F 2] : IsPGroup 2 (upperSpecial (d := d) (F := F)) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro g
  refine ⟨d, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact unitriangular_two_pow g.property

private theorem transvection_mem_upperSpecial [CharP F 2]
    {i j : Fin d} (hij : i < j) (c : F) :
    SpecialLinearGroup.transvection (ne_of_lt hij) c ∈ upperSpecial := by
  constructor
  · intro k l hkl
    change l < k at hkl
    change (1 + single i j c) k l = 0
    have hn : ¬ (i = k ∧ j = l) := by
      rintro ⟨rfl, rfl⟩
      exact (not_lt_of_ge (le_of_lt hij)) hkl
    simp [hn, ne_of_gt hkl]
  · intro k
    change (1 + single i j c) k k = 1
    have hn : ¬ (i = k ∧ j = k) := by
      rintro ⟨rfl, rfl⟩
      exact (lt_irrefl _) hij
    simp [hn]

/-- The actual positive-root subgroup is a two-group; no maximality assertion is needed. -/
theorem upperRoots_isPGroup [CharP F 2] : IsPGroup 2 (upperRoots d F) := by
  let f : SL(d,F) →* PSL(d,F) := QuotientGroup.mk' _
  have hle : upperRoots d F ≤ (upperSpecial (d := d) (F := F)).map f := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨i,j,hij,c,rfl⟩
    exact Subgroup.mem_map_of_mem f (transvection_mem_upperSpecial hij c)
  exact (upperSpecial_isPGroup.map f).of_injective
    (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
end Matrix.HigherLinear.SylowPointwiseInner
