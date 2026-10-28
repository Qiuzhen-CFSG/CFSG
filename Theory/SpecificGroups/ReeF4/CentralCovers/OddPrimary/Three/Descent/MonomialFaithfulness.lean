module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Unitary

/-!
# Faithfulness detected on the full unitary diagonal torus

The two coordinate permutations normalize the determinant-one norm-one
diagonal torus, so it is normal in the literal monomial subgroup. A kernel
disjoint from this torus centralizes it. Two diagonal matrices distinguish
every pair of coordinates, forcing the kernel to be diagonal and hence
trivial. In particular, retaining the full torus also retains the scalar
three-center. No group order or projective comparison is used.

This supplies the faithfulness step for the exceptional descent in GLS3,
Example 2.6.3 and Table 4.7.3A. The actual root-group construction remains
separate from this matrix argument.
-/

@[expose] public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary
namespace ReeF4.CentralCovers.OddPrimary.Three.Descent
noncomputable section
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 3 F) (hJ : J.form = 1)

abbrev NormParameters := HermitianForm.EvenInner.normOne J × HermitianForm.EvenInner.normOne J

/-- The full norm-one torus, including scalar matrices of order three. -/
def fullTorus : Subgroup (Unitary.monomial J hJ) := (Unitary.normDiagonal J hJ).range

theorem normDiagonal_injective : Function.Injective (Unitary.normDiagonal J hJ) := by
  intro a b h
  have he := congrArg (fun x : Unitary.monomial J hJ => x.val.val.val) h
  apply Prod.ext
  · apply Subtype.ext; apply Units.ext
    exact congrArg (fun A => A 0 0) he
  · apply Subtype.ext; apply Units.ext
    exact congrArg (fun A => A 2 2) he

theorem cycle_normDiagonal (a : NormParameters J) :
    Unitary.cycle J hJ * Unitary.normDiagonal J hJ a * (Unitary.cycle J hJ)⁻¹ =
      Unitary.normDiagonal J hJ ((a.1 * a.2)⁻¹, a.1) := by
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Unitary.cycle, Unitary.cycleSU, Unitary.normDiagonal,
      MatrixTorus.diagonalSpecial, MatrixTorus.diagonalGL_val, MatrixTorus.entries,
      MatrixTorus.cycleGL, Matrix.mul_apply, Fin.sum_univ_succ, mul_assoc, mul_comm]

theorem swap_normDiagonal (a : NormParameters J) :
    Unitary.swap J hJ * Unitary.normDiagonal J hJ a * (Unitary.swap J hJ)⁻¹ =
      Unitary.normDiagonal J hJ (a.2, a.1) := by
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Unitary.swap, Unitary.swapSU, Unitary.normDiagonal,
      MatrixTorus.diagonalSpecial, MatrixTorus.diagonalGL_val, MatrixTorus.entries,
      MatrixTorus.swapGL, Matrix.mul_apply, Fin.sum_univ_succ, mul_assoc, mul_comm]

/-- The literal generators generate the whole published monomial group. -/
theorem fullTorus_sup_permutations :
    fullTorus J hJ ⊔ (zpowers (Unitary.cycle J hJ) ⊔ zpowers (Unitary.swap J hJ)) = ⊤ := by
  apply Subgroup.map_injective (Unitary.monomial J hJ).subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  change ((Unitary.normDiagonal J hJ).range.map (Unitary.monomial J hJ).subtype) ⊔
      (zpowers (Unitary.cycleSU J hJ) ⊔ zpowers (Unitary.swapSU J hJ)) = _
  rw [MonoidHom.map_range]
  rfl

private theorem normalizes_range {G A : Type*} [Group G] [Group A]
    (d : A →* G) (g : G) (s : A → A) (hs : Function.Surjective s)
    (h : ∀ a, g * d a * g⁻¹ = d (s a)) : g ∈ normalizer (d.range : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨s a, (h a).symm⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := hs a
    refine ⟨b, ?_⟩
    have he := (h b).trans ha
    exact (MulAut.conj g).injective he

/-- Normality is relative to the actual monomial subgroup. -/
theorem fullTorus_normal : (fullTorus J hJ).Normal := by
  rw [← normalizer_eq_top_iff, ← top_le_iff, ← fullTorus_sup_permutations J hJ]
  refine sup_le (fullTorus J hJ).le_normalizer (sup_le ?_ ?_)
  · apply zpowers_le.mpr
    apply normalizes_range (Unitary.normDiagonal J hJ) _
      (fun a => ((a.1 * a.2)⁻¹, a.1)) _ (cycle_normDiagonal J hJ)
    rintro ⟨a, b⟩
    exact ⟨(b, (a * b)⁻¹), by simp [mul_comm]⟩
  · apply zpowers_le.mpr
    exact normalizes_range (Unitary.normDiagonal J hJ) _ Prod.swap
      (fun a => ⟨a.swap, rfl⟩) (swap_normDiagonal J hJ)

/-- Homomorphisms are determined by the complete torus and the two permutations. -/
theorem hom_ext {G : Type*} [Group G] (f g : Unitary.monomial J hJ →* G)
    (hd : ∀ a, f (Unitary.normDiagonal J hJ a) = g (Unitary.normDiagonal J hJ a))
    (hc : f (Unitary.cycle J hJ) = g (Unitary.cycle J hJ))
    (hs : f (Unitary.swap J hJ) = g (Unitary.swap J hJ)) : f = g := by
  have ht : (⊤ : Subgroup (Unitary.monomial J hJ)) ≤ f.eqLocus g := by
    rw [← fullTorus_sup_permutations J hJ]
    exact sup_le (by rintro _ ⟨a, rfl⟩; exact hd a)
      (sup_le (zpowers_le.mpr hc) (zpowers_le.mpr hs))
  exact MonoidHom.ext (fun x => ht (mem_top x))

private theorem diagonal_entry_zero (x : Unitary.monomial J hJ) (a : NormParameters J)
    (h : Commute x (Unitary.normDiagonal J hJ a)) (i j : Fin 3)
    (hne : ((MatrixTorus.entries _ a j).val : F) ≠ ((MatrixTorus.entries _ a i).val : F)) :
    x.val.val.val i j = 0 := by
  have he := congrArg (fun y : Unitary.monomial J hJ => y.val.val.val i j) h.eq
  change ((x.val.val.val : Matrix (Fin 3) (Fin 3) F) *
      Matrix.diagonal (fun k => ((MatrixTorus.entries _ a k).val : F))) i j =
    (Matrix.diagonal (fun k => ((MatrixTorus.entries _ a k).val : F)) *
      (x.val.val.val : Matrix (Fin 3) (Fin 3) F)) i j at he
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] at he
  exact (mul_eq_mul_right_iff.mp he).resolve_left hne

/-- Commuting with the full norm-one torus forces all off-diagonal entries to vanish. -/
theorem isDiag_of_commute_normDiagonal
    (u : HermitianForm.EvenInner.normOne J) (hu : u ≠ 1)
    (x : Unitary.monomial J hJ)
    (h : ∀ a, Commute x (Unitary.normDiagonal J hJ a)) : Matrix.IsDiag x.val.val.val := by
  have hune : (u.val : F) ≠ 1 := by
    intro he
    exact hu (Subtype.ext (Units.ext he))
  have huine : (u.val : F)⁻¹ ≠ 1 := by simpa using hune
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  · exact diagonal_entry_zero J hJ x (1, u) (h _) _ _ (by simpa [MatrixTorus.entries] using huine)
  · exact diagonal_entry_zero J hJ x (u, 1) (h _) _ _ (by simpa [MatrixTorus.entries] using hune.symm)
  · exact diagonal_entry_zero J hJ x (1, u) (h _) _ _ (by simpa [MatrixTorus.entries] using huine.symm)
  · exact diagonal_entry_zero J hJ x (u, 1) (h _) _ _ (by simpa [MatrixTorus.entries] using huine.symm)
  · exact diagonal_entry_zero J hJ x (u, 1) (h _) _ _ (by simpa [MatrixTorus.entries] using hune)
  · exact diagonal_entry_zero J hJ x (u, 1) (h _) _ _ (by simpa [MatrixTorus.entries] using huine)

/-- A diagonal matrix in the full special unitary group has the published two-parameter form. -/
theorem mem_fullTorus_of_isDiag (x : Unitary.monomial J hJ)
    (hx : Matrix.IsDiag x.val.val.val) : x ∈ fullTorus J hJ := by
  have hxdiag := hx.diagonal_diag
  obtain ⟨hn, hd⟩ := (HermitianForm.mem_specialSubgroup_iff J x.val.val).mp x.val.property
  rw [hJ, Matrix.mul_one, ← hxdiag] at hn
  have hn' (i : Fin 3) : J.conj (x.val.val.val i i) * x.val.val.val i i = 1 := by
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A i i) hn
    simpa [HermitianForm.conjTranspose, Matrix.mul_diagonal] using he
  have hne (i : Fin 3) : x.val.val.val i i ≠ 0 := by
    intro he
    simpa [he] using hn' i
  let a : HermitianForm.EvenInner.normOne J :=
    ⟨Units.mk0 (x.val.val.val 0 0) (hne 0), eq_inv_of_mul_eq_one_left (hn' 0)⟩
  let b : HermitianForm.EvenInner.normOne J :=
    ⟨Units.mk0 (x.val.val.val 2 2) (hne 2), eq_inv_of_mul_eq_one_left (hn' 2)⟩
  have hdet : x.val.val.val.det = 1 := congrArg Units.val hd
  rw [← hxdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have hmid : (x.val.val.val 0 0 * x.val.val.val 2 2)⁻¹ = x.val.val.val 1 1 := by
    apply inv_eq_of_mul_eq_one_left
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdet
  refine ⟨(a, b), ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  change Matrix.diagonal _ = x.val.val.val
  rw [← hxdiag]
  congr 1
  funext i
  fin_cases i
  · rfl
  · simpa [MatrixTorus.entries, a, b, Matrix.diag, mul_comm] using hmid
  · rfl

/-- A homomorphism is faithful as soon as it is faithful on the full diagonal torus.
The argument uses relative normality and its matrix centralizer; no projective quotient occurs. -/
theorem injective_of_normDiagonal {G : Type*} [Group G]
    (u : HermitianForm.EvenInner.normOne J) (hu : u ≠ 1)
    (f : Unitary.monomial J hJ →* G)
    (hf : Function.Injective (f.comp (Unitary.normDiagonal J hJ))) : Function.Injective f := by
  apply (injective_iff_map_eq_one f).mpr
  intro x hx
  have hn := fullTorus_normal J hJ
  have hc (a : NormParameters J) : Commute x (Unitary.normDiagonal J hJ a) := by
    obtain ⟨b, hb⟩ := hn.conj_mem (Unitary.normDiagonal J hJ a) ⟨a, rfl⟩ x
    have hab : b = a := hf (by
      change f (Unitary.normDiagonal J hJ b) = f (Unitary.normDiagonal J hJ a)
      rw [hb, map_mul, map_mul, map_inv, hx, one_mul, inv_one, mul_one])
    subst b
    exact mul_inv_eq_iff_eq_mul.mp hb.symm
  obtain ⟨a, rfl⟩ := mem_fullTorus_of_isDiag J hJ x
    (isDiag_of_commute_normDiagonal J hJ u hu x hc)
  have ha : a = 1 := hf (by simpa using hx)
  rw [ha, map_one]

end
end ReeF4.CentralCovers.OddPrimary.Three.Descent
