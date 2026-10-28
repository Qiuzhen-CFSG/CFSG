module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Monomial.CubeLine

/-!
# Monomial conjugation of the projective cube-root element

A matrix stabilizing the punctured coordinate axes has one nonzero entry
in each column. Invertibility makes the resulting map on coordinates a
permutation. The six permutations carry diag(a, a⁻¹, 1), for a³ = 1, to
itself or its inverse up to a scalar cube root of unity. The scalar lies
in the full center of SL₃ and disappears under the actual projection to PSL₃.

The column-support argument follows the private coordinate calculation in
`Theory.SpecificGroups.SL3.SplitMonomial.LocalCore.LinearFour`; the argument
here uses only the defining monomial stabilizer and the scalar quotient.

Source: the split decomposition stabilizer in GLS3, Theorem 6.5.3(b),
`refs/KGroup/GLS3/chapter6.tex`, used in Aschbacher–Smith, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

public section

open Subgroup Matrix
open scoped MatrixGroups Pointwise
open Matrix.SL3.SplitMonomial

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial.Monomial

variable {F : Type*} [Field F]

private theorem column_support (g : linear F) (j : Fin 3) :
    ∃ i, g.val i j ≠ 0 ∧ ∀ r, r ≠ i → g.val r j = 0 := by
  have hstab : g.val • coordinateVectors F = coordinateVectors F :=
    MulAction.mem_stabilizer_iff.mp g.property
  have hv : g.val • Pi.single j (1 : F) ∈ coordinateVectors F := by
    rw [← hstab]
    exact Set.smul_mem_smul_set (single_mem_coordinateVectors F j one_ne_zero)
  change g.val.val *ᵥ Pi.single j 1 ∈ coordinateVectors F at hv
  simpa only [Matrix.mulVec_single_one, coordinateVectors, Set.mem_ofPred_eq,
    Matrix.col_apply] using hv

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

private theorem cube_permutation (a : Fˣ) (ha : a ^ 3 = 1) (σ : Equiv.Perm (Fin 3)) :
    ∃ b : Fˣ, (b = a ∨ b = a⁻¹) ∧ ∃ c : Fˣ, c ^ 3 = 1 ∧
      ∀ j : Fin 3, ![a, a⁻¹, 1] j = c * ![b, b⁻¹, 1] (σ j) := by
  have hs : a * a = a⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [pow_succ, pow_zero, one_mul] using ha
  have hi : a⁻¹ ^ 3 = 1 := by rw [inv_pow, ha, inv_one]
  have hsi : a⁻¹ * a⁻¹ = a := by
    apply inv_inj.mp
    simpa using hs
  have h01 := σ.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := σ.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := σ.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hp :
      (σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2) ∨
      (σ 0 = 0 ∧ σ 1 = 2 ∧ σ 2 = 1) ∨
      (σ 0 = 1 ∧ σ 1 = 0 ∧ σ 2 = 2) ∨
      (σ 0 = 1 ∧ σ 1 = 2 ∧ σ 2 = 0) ∨
      (σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 1) ∨
      (σ 0 = 2 ∧ σ 1 = 1 ∧ σ 2 = 0) := by
    generalize h0 : σ 0 = i0 at *
    generalize h1 : σ 1 = i1 at *
    generalize h2 : σ 2 = i2 at *
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> simp_all
  rcases hp with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · refine ⟨a, Or.inl rfl, 1, one_pow _, ?_⟩
    intro j
    fin_cases j <;> simp [h0, h1, h2]
  · refine ⟨a⁻¹, Or.inr rfl, a⁻¹, hi, ?_⟩
    intro j
    fin_cases j <;> simp [h0, h1, h2, hsi]
  · refine ⟨a⁻¹, Or.inr rfl, 1, one_pow _, ?_⟩
    intro j
    fin_cases j <;> simp [h0, h1, h2]
  · refine ⟨a, Or.inl rfl, a⁻¹, hi, ?_⟩
    intro j
    fin_cases j <;> simp [h0, h1, h2, hsi]
  · refine ⟨a, Or.inl rfl, a, ha, ?_⟩
    intro j
    fin_cases j <;> simp [h0, h1, h2, hs]
  · refine ⟨a⁻¹, Or.inr rfl, a, ha, ?_⟩
    intro j
    fin_cases j <;> simp [h0, h1, h2, hs]

private theorem projective_conj_of_coordinates (g : linear F) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ i j, i ≠ σ j → g.val i j = 0)
    (a b c : Fˣ) (hc : c ^ 3 = 1)
    (hd : ∀ j : Fin 3, ![a, a⁻¹, 1] j = c * ![b, b⁻¹, 1] (σ j)) :
    Matrix.PSL3.projection F g.val * cubeElement a *
      (Matrix.PSL3.projection F g.val)⁻¹ = cubeElement b := by
  have hcF : (c : F) ^ 3 = 1 := congrArg Units.val hc
  let z : SL(3,F) := ⟨Matrix.scalar (Fin 3) (c : F), by
    simpa [Matrix.scalar, Matrix.det_diagonal, Fin.prod_univ_three, pow_succ] using hcF⟩
  have hz : Matrix.PSL3.projection F z = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨(c : F), hcF, rfl⟩
  have cast_vec (x : Fˣ) (j : Fin 3) :
      ((![x, x⁻¹, 1] j : Fˣ) : F) = ![(x : F), (x⁻¹ : Fˣ), 1] j := by
    fin_cases j <;> rfl
  have hdF (j : Fin 3) : ![(a : F), (a⁻¹ : Fˣ), 1] j =
      (c : F) * ![(b : F), (b⁻¹ : Fˣ), 1] (σ j) := by
    simpa only [Units.val_mul, cast_vec] using congrArg Units.val (hd j)
  have he : g.val * cubeSL a = z * cubeSL b * g.val := by
    apply Subtype.ext
    change g.val.val * Matrix.diagonal _ =
      (Matrix.diagonal (fun _ : Fin 3 => (c : F)) * Matrix.diagonal _) * g.val.val
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : i = σ j
    · subst i
      change g.val (σ j) j * _ = ((c : F) * _) * g.val (σ j) j
      rw [hdF j]
      exact mul_comm _ _
    · change g.val i j * _ = _ * g.val i j
      rw [hσ i j hij, zero_mul, mul_zero]
  apply mul_inv_eq_iff_eq_mul.mpr
  simpa only [map_mul, hz, one_mul, cubeElement] using congrArg (Matrix.PSL3.projection F) he

/-- Every element of the actual projective monomial subgroup fixes or inverts
the cube-root element under conjugation, including the scalar corrections
for the three-cycles. -/
theorem cubeElement_conj_eq_or_inv [Finite F]
    (a : Fˣ) (ha : a ^ 3 = 1) (g : PSL(3,F))
    (hg : g ∈ Matrix.SL3.SplitMonomial.projective F) :
    g * cubeElement a * g⁻¹ = cubeElement a ∨
      g * cubeElement a * g⁻¹ = (cubeElement a)⁻¹ := by
  obtain ⟨x, hx, rfl⟩ := hg
  let y : linear F := ⟨x, hx⟩
  obtain ⟨σ, hσ⟩ := exists_column_permutation y
  obtain ⟨b, hb, c, hc, hd⟩ := cube_permutation a ha σ
  have he := projective_conj_of_coordinates y σ hσ a b c hc hd
  rcases hb with rfl | rfl
  · exact Or.inl he
  · right
    exact he.trans (map_inv (cubeHom (F := F)) a)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial.Monomial
