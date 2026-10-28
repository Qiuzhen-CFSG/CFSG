module

public import Theory.SpecificGroups.SL3.SplitMonomial
public import Theory.SpecificGroups.ProjectiveLinearInvolutions
import Mathlib.Data.Set.Card

/-!
# The normal diagonal four-subgroup of split monomial SL₃

The identity and the three diagonal matrices with one positive and two
negative signs form a subgroup of the stabilizer of punctured coordinate
axes. Each stabilizer element has exactly one nonzero entry in each
column; invertibility makes the support map a permutation of the axes.
Conjugation therefore permutes the three sign matrices. In characteristic
different from two, commuting with these signs forces every off-diagonal
entry to vanish, so their relative centralizer is abelian.

This supplies the concrete linear witness for the local three-core
calculation used in Aschbacher–Smith, *The Classification of Quasithin
Groups*, printed p.511 (PDF p.528). The decomposition stabilizer is the
split linear case of GLS3, Theorem 6.5.3(b),
`refs/KGroup/GLS3/chapter6.tex`.
-/

public section

open Matrix
open scoped Pointwise
namespace Matrix.SL3.SplitMonomial
variable {F : Type*} [Field F]

private def diagonalSign (k : Fin 3) : SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal (fun i => if i = k then 1 else -1), by
    fin_cases k <;> simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

private theorem diagonalSign_mul_self (k : Fin 3) :
    diagonalSign (F := F) k * diagonalSign k = 1 := by
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hi : i = k <;> by_cases hij : i = j <;>
    simp_all [Matrix.one_apply]

private theorem diagonalSign_inv (k : Fin 3) :
    (diagonalSign (F := F) k)⁻¹ = diagonalSign k :=
  inv_eq_of_mul_eq_one_left (diagonalSign_mul_self k)

private theorem diagonalSign_preserves (k : Fin 3) {v : Fin 3 → F}
    (hv : v ∈ coordinateVectors F) : diagonalSign (F := F) k • v ∈ coordinateVectors F := by
  obtain ⟨i, hi, hv⟩ := hv
  change ∃ i, (Matrix.diagonal (fun r => if r = k then (1 : F) else -1) *ᵥ v) i ≠ 0 ∧ _
  refine ⟨i, ?_, ?_⟩
  · simpa only [Matrix.mulVec_diagonal, Pi.mul_apply] using
      mul_ne_zero (show (if i = k then (1 : F) else -1) ≠ 0 by split_ifs <;> simp) hi
  · intro j hj
    change (Matrix.diagonal (fun r => if r = k then (1 : F) else -1) *ᵥ v) j = 0
    simp [Matrix.mulVec_diagonal, hv j hj]

private theorem diagonalSign_mem (k : Fin 3) : diagonalSign (F := F) k ∈ linear F := by
  change diagonalSign k ∈ MulAction.stabilizer _ (coordinateVectors F)
  rw [MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · exact Set.smul_set_subset_iff.mpr (fun _ hv => diagonalSign_preserves k hv)
  · rw [Set.subset_smul_set_iff, diagonalSign_inv]
    exact Set.smul_set_subset_iff.mpr (fun _ hv => diagonalSign_preserves k hv)

private def linearSign (k : Fin 3) : linear F := ⟨diagonalSign k, diagonalSign_mem k⟩

private theorem linearSign_mul_self (k : Fin 3) :
    linearSign (F := F) k * linearSign k = 1 :=
  Subtype.ext (diagonalSign_mul_self k)

private theorem linearSign_inv (k : Fin 3) :
    (linearSign (F := F) k)⁻¹ = linearSign k :=
  inv_eq_of_mul_eq_one_left (linearSign_mul_self k)

private theorem linearSign_mul (i j : Fin 3) :
    linearSign (F := F) i * linearSign j = 1 ∨
      ∃ k, linearSign (F := F) i * linearSign j = linearSign k := by
  by_cases h : i = j
  · subst j
    exact Or.inl (linearSign_mul_self i)
  · right
    fin_cases i <;> fin_cases j
    all_goals try exact (h rfl).elim
    case' «0».«1» => refine ⟨2, ?_⟩
    case' «0».«2» => refine ⟨1, ?_⟩
    case' «1».«0» => refine ⟨2, ?_⟩
    case' «1».«2» => refine ⟨0, ?_⟩
    case' «2».«0» => refine ⟨1, ?_⟩
    case' «2».«1» => refine ⟨0, ?_⟩
    all_goals
      apply Subtype.ext
      apply Subtype.ext
      change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      ext r
      fin_cases r <;> simp

private def linearFour : Subgroup (linear F) where
  carrier := {x | x = 1 ∨ ∃ k, x = linearSign k}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | ⟨i, rfl⟩) (rfl | ⟨j, rfl⟩)
    · exact Or.inl (one_mul 1)
    · exact Or.inr ⟨j, one_mul _⟩
    · exact Or.inr ⟨i, mul_one _⟩
    · exact linearSign_mul i j
  inv_mem' := by
    rintro a (rfl | ⟨i, rfl⟩)
    · exact Or.inl inv_one
    · exact Or.inr ⟨i, linearSign_inv i⟩

private theorem linearSign_ne_one (h2 : (2 : F) ≠ 0) (k : Fin 3) :
    linearSign (F := F) k ≠ 1 := by
  intro h
  have hh (i : Fin 3) := congrArg (fun x : linear F => x.val i i) h
  fin_cases k
  · have he := hh 1
    change (-1 : F) = 1 at he
    apply h2
    linear_combination -he
  · have he := hh 0
    change (-1 : F) = 1 at he
    apply h2
    linear_combination -he
  · have he := hh 0
    change (-1 : F) = 1 at he
    apply h2
    linear_combination -he

private theorem linearSign_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (linearSign (F := F)) := by
  intro i j h
  by_contra hij
  have he := congrArg (fun x : linear F => x.val i i) h
  simp [linearSign, diagonalSign, hij] at he
  apply h2
  linear_combination he

private theorem linearFour_card (h2 : (2 : F) ≠ 0) :
    Nat.card (linearFour (F := F)) = 4 := by
  change (linearFour (F := F) : Set (linear F)).ncard = 4
  apply Set.ncard_eq_four.mpr
  refine ⟨1, linearSign 0, linearSign 1, linearSign 2,
    (linearSign_ne_one h2 0).symm, (linearSign_ne_one h2 1).symm,
    (linearSign_ne_one h2 2).symm,
    (linearSign_injective h2).ne (by decide),
    (linearSign_injective h2).ne (by decide),
    (linearSign_injective h2).ne (by decide), ?_⟩
  ext x
  change (x = 1 ∨ ∃ k, x = linearSign k) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_succ,
    Fin.exists_fin_zero, or_false]
  rfl

private theorem column_support (g : linear F) (j : Fin 3) :
    ∃ i, g.val i j ≠ 0 ∧ ∀ r, r ≠ i → g.val r j = 0 := by
  have hstab : g.val • coordinateVectors F = coordinateVectors F :=
    MulAction.mem_stabilizer_iff.mp g.property
  have hv : g.val • Pi.single j (1 : F) ∈ coordinateVectors F := by
    rw [← hstab]
    exact Set.smul_mem_smul_set (single_mem_coordinateVectors F j one_ne_zero)
  simpa only [SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec,
    Matrix.mulVec_single_one, coordinateVectors, Set.mem_ofPred_eq, Matrix.col_apply] using hv

private theorem exists_column_permutation (g : linear F) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i j, i ≠ σ j → g.val i j = 0 := by
  classical
  let p : Fin 3 → Fin 3 := fun j => (column_support g j).choose
  have hp (j r : Fin 3) (h : r ≠ p j) : g.val r j = 0 :=
    (column_support g j).choose_spec.2 r h
  have hs : Function.Surjective p := by
    intro i
    by_contra h
    have hz (j : Fin 3) : g.val i j = 0 := hp j i (fun he => h ⟨j, he.symm⟩)
    have hh := congrArg (fun A : SpecialLinearGroup (Fin 3) F => A i i)
      (mul_inv_cancel g.val)
    change (g.val.val * (g.val⁻¹).val) i i = (1 : Matrix (Fin 3) (Fin 3) F) i i at hh
    simp only [Matrix.one_apply_eq, Matrix.mul_apply, hz, zero_mul, Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective p
    ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  exact ⟨σ, fun i j hij => hp j i hij⟩

private theorem conjugate_linearSign (g : linear F) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k,
      g * linearSign k * g⁻¹ = linearSign (σ k) := by
  obtain ⟨σ, hσ⟩ := exists_column_permutation g
  refine ⟨σ, fun k => ?_⟩
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Subtype.ext
  change g.val.val * Matrix.diagonal _ = Matrix.diagonal _ * g.val.val
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = σ j
  · subst i
    by_cases hjk : j = k
    · subst j
      simp
    · simp [hjk, σ.injective.ne hjk]
  · change g.val i j * _ = _ * g.val i j
    rw [hσ i j hij, zero_mul, mul_zero]

private theorem linearFour_normal : (linearFour (F := F)).Normal := by
  constructor
  intro x hx g
  rcases hx with rfl | ⟨k, rfl⟩
  · exact Or.inl (by simp)
  · obtain ⟨σ, hσ⟩ := conjugate_linearSign g
    exact Or.inr ⟨σ k, hσ k⟩

private theorem centralizer_off_diagonal (h2 : (2 : F) ≠ 0)
    (g : linear F) (hg : g ∈ Subgroup.centralizer (linearFour (F := F) : Set (linear F)))
    (i j : Fin 3) (hij : i ≠ j) : g.val i j = 0 := by
  have hc : linearSign i * g = g * linearSign i := hg (linearSign i) (Or.inr ⟨i, rfl⟩)
  have he := congrArg (fun A : linear F => A.val i j) hc
  change (Matrix.diagonal (fun r => if r = i then (1 : F) else -1) * g.val.val) i j =
    (g.val.val * Matrix.diagonal (fun r => if r = i then (1 : F) else -1)) i j at he
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  simp [hij.symm] at he
  apply (mul_eq_zero.mp (show (2 : F) * g.val i j = 0 by linear_combination he)).resolve_left h2

private theorem linearFour_centralizer_commutative (h2 : (2 : F) ≠ 0) :
    IsMulCommutative (Subgroup.centralizer (linearFour (F := F) : Set (linear F))) := by
  apply IsMulCommutative.of_setLike_mul_comm
  intro a ha b hb
  have hdiag (g : linear F)
      (hg : g ∈ Subgroup.centralizer (linearFour (F := F) : Set (linear F))) :
      g.val.val = Matrix.diagonal (fun i => g.val i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simpa [Matrix.diagonal_apply, hij] using centralizer_off_diagonal h2 g hg i j hij
  apply Subtype.ext
  apply Subtype.ext
  change a.val.val * b.val.val = b.val.val * a.val.val
  rw [hdiag a ha, hdiag b hb, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

variable (F)

/-- Over a finite field of odd order, the split monomial subgroup contains
an actual normal diagonal sign subgroup of order four with abelian
centralizer inside the monomial subgroup. -/
theorem linear_normal_four [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ V : Subgroup (linear F), V.Normal ∧ Nat.card V = 4 ∧
      IsMulCommutative (Subgroup.centralizer (V : Set (linear F))) := by
  have h2 := Field.two_ne_zero_of_odd_card F hodd
  exact ⟨linearFour, linearFour_normal, linearFour_card h2,
    linearFour_centralizer_commutative h2⟩

end Matrix.SL3.SplitMonomial
