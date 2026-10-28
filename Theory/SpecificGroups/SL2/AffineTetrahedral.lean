module

public import Theory.SpecificGroups.SL2.BinaryTetrahedralHom
public import Theory.SpecificGroups.SL2.SL23IntoSL25
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Binary tetrahedral subgroups over odd prime characteristic

Choose a² + b² = -1 in the prime subfield. The matrices
I = [[0,1],[-1,0]] and J = [[a,b],[b,-a]] generate a quaternion group.
The matrix (-1 + I - J + JI)/2 has order three and induces the required
cycle of quaternion generators. The binary tetrahedral presentation
therefore maps to SL₂(F). Every nontrivial normal subgroup of the
24-element presentation contains its central involution, and that
involution maps to -1, so the map is injective.

Only the small abstract quaternion semidirect product is enumerated;
no enumeration of the target field or matrix group is needed. This supplies
the natural extension's order-24 actors for the last sentence of
Aschbacher–Smith, Lemma 8.2.7, printed p.718 (combined manuscript,
1 March 2004). The presentation and its generator convention come from
`BinaryTetrahedralHom.lean` and the extracted GLS3 5.2.4 model.
-/

public section
open Matrix
open GLS3.Chapter5.SchurPresentation
namespace Matrix.SpecialLinearGroup.AffineTetrahedral

private abbrev BI : BinaryTetrahedral := SemidirectProduct.inl (QuaternionGroup.a 1)
private abbrev BZ : BinaryTetrahedral := BI ^ 2
private instance : Fintype BinaryTetrahedral :=
  Fintype.ofEquiv (QuaternionGroup 2 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

private theorem detects_center (x : BinaryTetrahedral) :
    x = 1 ∨ x = BZ ∨ x ^ 2 = BZ ∨ x ^ 3 = BZ ∨
      (x * BI * x⁻¹ * BI⁻¹) ^ 2 = BZ := by
  revert x
  decide +kernel

private theorem injective_of_detects_center {H : Type*} [Group H]
    (f : BinaryTetrahedral →* H) (hf : f BZ ≠ 1) : Function.Injective f := by
  apply (injective_iff_map_eq_one f).mpr
  intro x hx
  rcases detects_center x with h | h | h | h | h
  · exact h
  all_goals exfalso; apply hf
  · simpa [h] using hx
  · have hh := congrArg f h
    simpa [map_pow, hx] using hh.symm
  · have hh := congrArg f h
    simpa [map_pow, hx] using hh.symm
  · have hh := congrArg f h
    simpa [map_pow, map_mul, map_inv, hx] using hh.symm

variable {F : Type*} [Field F]
private def I : SpecialLinearGroup (Fin 2) F := ⟨!![0,1; -1,0], by simp⟩
private def J (a b : F) (h : a ^ 2 + b ^ 2 = -1) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![a,b; b,-a], by simp [det_fin_two]; linear_combination -h⟩
private def T (a b : F) (h : a ^ 2 + b ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    SpecialLinearGroup (Fin 2) F :=
  ⟨!![(-1-a-b)/2,(1-b+a)/2; (-1-b+a)/2,(-1+a+b)/2], by
    simp only [det_fin_two, of_apply, cons_val_zero, cons_val_one]
    field_simp
    linear_combination -2 * h⟩

private theorem I_sq : (I : SpecialLinearGroup (Fin 2) F) ^ 2 = -1 := by
  apply Subtype.ext
  change (!![0,1; -1,0] : Matrix (Fin 2) (Fin 2) F) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

private theorem J_sq (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    J a b h ^ 2 = I ^ 2 := by
  rw [I_sq]
  apply Subtype.ext
  change (!![a,b; b,-a] : Matrix (Fin 2) (Fin 2) F) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    grind

private theorem JI (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    J a b h * I = I⁻¹ * J a b h := by
  apply Subtype.ext
  change (!![a,b; b,-a] : Matrix (Fin 2) (Fin 2) F) * !![0,1; -1,0] =
    adjugate !![0,1; -1,0] * !![a,b; b,-a]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

private theorem T_cube (a b : F) (h : a ^ 2 + b ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    T a b h h2 ^ 3 = 1 := by
  apply Subtype.ext
  change (!![(-1-a-b)/2,(1-b+a)/2; (-1-b+a)/2,(-1+a+b)/2] :
    Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals grind

private theorem T_conj_I (a b : F) (h : a ^ 2 + b ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    T a b h h2 * I * (T a b h h2)⁻¹ = J a b h * I := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  change (!![(-1-a-b)/2,(1-b+a)/2; (-1-b+a)/2,(-1+a+b)/2] :
    Matrix (Fin 2) (Fin 2) F) * !![0,1; -1,0] =
    (!![a,b; b,-a] * !![0,1; -1,0]) *
      !![(-1-a-b)/2,(1-b+a)/2; (-1-b+a)/2,(-1+a+b)/2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals grind

private theorem T_conj_J (a b : F) (h : a ^ 2 + b ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    T a b h h2 * J a b h * (T a b h h2)⁻¹ = I⁻¹ := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  change (!![(-1-a-b)/2,(1-b+a)/2; (-1-b+a)/2,(-1+a+b)/2] :
    Matrix (Fin 2) (Fin 2) F) * !![a,b; b,-a] =
    adjugate !![0,1; -1,0] *
      !![(-1-a-b)/2,(1-b+a)/2; (-1-b+a)/2,(-1+a+b)/2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals grind

/-- SL₂ over a field of prime characteristic greater than three contains a subgroup of order 24. -/
theorem exists_subgroup_card_twentyFour {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : 3 < p) : ∃ C : Subgroup (SpecialLinearGroup (Fin 2) F), Nat.card C = 24 := by
  obtain ⟨a0, b0, hab⟩ := CharP.sq_add_sq F p (-1)
  let a : F := a0
  let b : F := b0
  have h : a ^ 2 + b ^ 2 = -1 := by simpa [a, b] using hab
  have h2 : (2 : F) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
      ((CharP.cast_eq_zero_iff F p 2).mp hz)
  obtain ⟨f, hfI, _, _⟩ := exists_binaryTetrahedral_hom (I : SpecialLinearGroup (Fin 2) F)
    (J a b h) (T a b h h2)
    (by rw [show 4 = 2 * 2 by decide, pow_mul, I_sq]; simp)
    (J_sq a b h) (JI a b h) (T_cube a b h h2) (T_conj_I a b h h2) (T_conj_J a b h h2)
  have hf : Function.Injective f := by
    apply injective_of_detects_center f
    intro hz
    have he : (-1 : SpecialLinearGroup (Fin 2) F) = 1 := by
      simpa only [BZ, map_pow, hfI, I_sq] using hz
    have he0 := congrArg (fun g : SpecialLinearGroup (Fin 2) F => g.val 0 0) he
    change (-1 : F) = 1 at he0
    apply h2
    linear_combination -he0
  refine ⟨f.range, ?_⟩
  calc
    Nat.card f.range = Nat.card BinaryTetrahedral := (Nat.card_congr (Equiv.ofInjective f hf)).symm
    _ = 24 := by rw [SemidirectProduct.card]; norm_num [QuaternionGroup.card]

end Matrix.SpecialLinearGroup.AffineTetrahedral
