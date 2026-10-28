module

public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Three explicit involutions generate SL₃ over an odd prime field

Let A = diag(-1,-1,1), let B interchange the last two coordinates and
negate the first, and put C = [[0,1,1],[1,0,1],[0,0,-1]]. These are
involutions. For U = (AC)² and D = BAB, direct multiplication gives
UDUD = I + 4E₀₂. Since the field has odd prime order, powers give every
transvection in this root group. Conjugation by B and C gives two more
root groups and recovers the signed coordinate interchange S. Further
conjugations give all six roots, so elementary-matrix induction proves
generation of the actual special linear group.

This is a uniform odd-prime auxiliary calculation for the inner branch of
Guralnick–Malle, *Classification of 2F-modules I*, (2.6) and Proposition 4.2,
manuscript pp.4 and 9–10, used in Aschbacher–Smith K.2, p.453. GM02 states
the three-involution count explicitly at p = 3; the calculation here proves
the requested uniform extension without a simplicity hypothesis.
-/

public section

set_option backward.isDefEq.respectTransparency false

open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.OddPrimeConjugateBounds.InnerGenerators
variable (F : Type*) [Field F]

private def a : SL(3,F) := SL3.standardInvolution F
private def b : SL(3,F) :=
  ⟨!![-1, 0, 0; 0, 0, 1; 0, 1, 0], by simp [Matrix.det_fin_three]⟩
private def c : SL(3,F) :=
  ⟨!![0, 1, 1; 1, 0, 1; 0, 0, -1], by simp [Matrix.det_fin_three]⟩
private def s : SL(3,F) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

private theorem b_sq : b F ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b, Matrix.mul_apply, Fin.sum_univ_three]

private theorem c_sq : c F ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c, Matrix.mul_apply, Fin.sum_univ_three]

private theorem root_word :
    let u := (a F * c F) ^ 2
    let d := b F * a F * b F
    u * d * u * d = SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (4 : F) := by
  dsimp only
  rw [pow_two]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a, b, c, SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]
  norm_num

private theorem s_word :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : F) *
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F) * c F = s F := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s, c, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

private theorem c_root (x : F) :
    c F * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (-x) * c F =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) x := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

private theorem b_root02 (x : F) :
    b F * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (-x) * b F =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) x := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

private theorem b_root12 (x : F) :
    b F * SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) x * b F =
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) x := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

private theorem s_root21 (x : F) :
    s F * SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (-x) * s F =
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) x := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

private theorem b_root20 (x : F) :
    b F * SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (-x) * b F =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) x := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

private theorem root_nat_mul {i j : Fin 3} (hij : i ≠ j) (n : ℕ) (x : F) :
    SpecialLinearGroup.transvection hij ((n : F) * x) =
      SpecialLinearGroup.transvection hij x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, SpecialLinearGroup.transvection_add, ih, pow_succ]

private theorem eq_top_of_mem [Finite F] {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    (h2 : (2 : F) ≠ 0) (H : Subgroup SL(3,F))
    (ha : a F ∈ H) (hb : b F ∈ H) (hc : c F ∈ H) : H = ⊤ := by
  have h4 : (4 : F) ≠ 0 := by
    have := mul_ne_zero h2 h2
    norm_num at this ⊢
    exact this
  have hr : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (4 : F) ∈ H := by
    rw [← root_word]
    exact H.mul_mem (H.mul_mem (H.mul_mem
      (H.pow_mem (H.mul_mem ha hc) 2) (H.mul_mem (H.mul_mem hb ha) hb))
      (H.pow_mem (H.mul_mem ha hc) 2)) (H.mul_mem (H.mul_mem hb ha) hb)
  have h02 (x : F) :
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) x ∈ H := by
    let := Fintype.ofFinite F
    let : NeZero p := ⟨hp.ne_zero⟩
    let e := ZMod.ringEquivOfPrime F hp (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨z, hz⟩ := e.surjective (x / 4)
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
    have hn : (n : F) * 4 = x := by
      rw [← map_natCast e n, hz, div_mul_cancel₀ _ h4]
    rw [← hn, root_nat_mul]
    exact H.pow_mem hr n
  have h12 (x : F) :
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) x ∈ H := by
    rw [← c_root]
    exact H.mul_mem (H.mul_mem hc (h02 (-x))) hc
  have hs : s F ∈ H := by
    rw [← s_word]
    exact H.mul_mem (H.mul_mem (h02 1) (h12 1)) hc
  have h01 (x : F) :
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) x ∈ H := by
    rw [← b_root02]
    exact H.mul_mem (H.mul_mem hb (h02 (-x))) hb
  have h21 (x : F) :
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) x ∈ H := by
    rw [← b_root12]
    exact H.mul_mem (H.mul_mem hb (h12 x)) hb
  have h20 (x : F) :
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) x ∈ H := by
    rw [← s_root21]
    exact H.mul_mem (H.mul_mem hs (h21 (-x))) hs
  have h10 (x : F) :
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) x ∈ H := by
    rw [← b_root20]
    exact H.mul_mem (H.mul_mem hb (h20 (-x))) hb
  apply top_unique
  intro g _
  apply Representation.OneCohomology.SLHigherNatural.transvection_induction
    (fun g => g ∈ H) ?_ (fun _ _ => H.mul_mem) g
  intro i j hij x
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact h01 x
    | exact h02 x
    | exact h10 x
    | exact h12 x
    | exact h20 x
    | exact h21 x

/-- Three actual involutions generate the whole determinant-one matrix group. -/
theorem exists_generating_involutions [Finite F] {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p) (h2 : (2 : F) ≠ 0) :
    ∃ t : Fin 3 → SL(3,F), (∀ i, orderOf (t i) = 2) ∧
      closure (Set.range t) = ⊤ := by
  refine ⟨![a F, b F, c F], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact SL3.standardInvolution_orderOf F h2
    · apply orderOf_eq_prime (b_sq F)
      intro h
      have he := congrArg (fun x : SL(3,F) => x.val 1 2) h
      have : (1 : F) = 0 := he
      exact one_ne_zero this
    · apply orderOf_eq_prime (c_sq F)
      intro h
      have he := congrArg (fun x : SL(3,F) => x.val 0 1) h
      have : (1 : F) = 0 := he
      exact one_ne_zero this
  · apply eq_top_of_mem F hp hF h2
    · exact subset_closure ⟨0, rfl⟩
    · exact subset_closure ⟨1, rfl⟩
    · exact subset_closure ⟨2, rfl⟩

end Matrix.PSL3.OddPrimeConjugateBounds.InnerGenerators
