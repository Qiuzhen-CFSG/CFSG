module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootCoordinates

/-!
# Root-preserving automorphisms over prime fields are diagonal

Each coordinate root group is cyclic of prime order. Its preserved generator
therefore acquires a nonzero scalar. The three-index elementary relation forces
these scalars to be ratios of three diagonal entries. Generation by elementary
matrices identifies the original projective automorphism with conjugation by
this diagonal GL₃ matrix.

The argument includes characteristic three and uses neither simplicity nor a
lift from PSL₃ to SL₃. It is the reconstruction step for GLS3, Theorem 2.5.12(a),
with the concrete matrix convention in §2.7, lines 1111–1115 of
`refs/KGroup/GLS3/chapter2.tex`. Preservation of the six root groups is an
explicit hypothesis here; arbitrary-automorphism normalization remains separate.
-/

@[expose] public section

open scoped MatrixGroups
open Matrix
namespace Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable {F : Type*} [Field F]

/-- The invertible diagonal matrix with the specified three unit entries. -/
def diagonalGL (d : Fin 3 → Fˣ) : GL (Fin 3) F where
  val := Matrix.diagonal (fun i => (d i).val)
  inv := Matrix.diagonal (fun i => ((d i)⁻¹).val)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

theorem linearConj_diagonalGL_rootElement (d : Fin 3 → Fˣ)
    {i j : Fin 3} (hij : i ≠ j) (a : F) :
    linearConj F (diagonalGL d) (rootElement hij a) =
      rootElement hij (a * (d i : F) * ((d j)⁻¹ : Fˣ)) := by
  change QuotientGroup.mk (linearConjSL F (diagonalGL d)
    (SpecialLinearGroup.transvection hij a)) = _
  apply congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F))
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL]
  apply Units.ext
  change Matrix.diagonal (fun r => (d r).val) * (1 + Matrix.single i j a) *
    Matrix.diagonal (fun s => ((d s)⁻¹).val) =
      1 + Matrix.single i j (a * (d i : F) * ((d j)⁻¹ : Fˣ))
  ext r s
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply]
  by_cases hr : r = i <;> by_cases hs : s = j <;> by_cases hrs : r = s <;>
    simp_all [Matrix.one_apply, Matrix.single_apply, mul_assoc, mul_comm]

/-- Setwise preservation of each of the six actual coordinate root groups. -/
def PreservesRootGroups (α : MulAut PSL(3,F)) : Prop :=
  ∀ (i j : Fin 3) (hij : i ≠ j), (rootGroup (F := F) hij).map α.toMonoidHom = rootGroup hij

theorem exists_root_scalar (α : MulAut PSL(3,F)) (hα : PreservesRootGroups α)
    {i j : Fin 3} (hij : i ≠ j) :
    ∃ c : Fˣ, α (rootElement hij 1) = rootElement hij (c : F) := by
  have hm : α (rootElement hij 1) ∈ rootGroup hij := by
    rw [← hα i j hij]
    exact Subgroup.mem_map_of_mem α.toMonoidHom (rootElement_mem hij 1)
  obtain ⟨c, hc⟩ := hm
  change rootElement hij c.toAdd = α (rootElement hij 1) at hc
  have hn : c.toAdd ≠ 0 := by
    intro h
    have he : α (rootElement hij 1) = 1 := by
      simpa only [h, rootElement_zero] using hc.symm
    have he' : rootElement (F := F) hij 1 = 1 := α.injective (he.trans (map_one α).symm)
    exact one_ne_zero ((rootElement_eq_one_iff hij 1).mp he')
  exact ⟨Units.mk0 c.toAdd hn, hc.symm⟩

theorem root_scalar_chain (α : MulAut PSL(3,F))
    (c : ∀ (i j : Fin 3), i ≠ j → Fˣ)
    (hc : ∀ (i j : Fin 3) (hij : i ≠ j), α (rootElement hij 1) = rootElement hij (c i j hij : F))
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    c i j hij * c j k hjk = c i k hik := by
  have h := congrArg α (rootElement_chain (F := F) hij hjk hik 1 1)
  simp only [map_mul, one_mul, hc] at h
  have h' := (rootElement_chain hij hjk hik (c i j hij : F) (c j k hjk : F)).symm.trans h
  exact Units.ext (rootElement_injective hik (mul_left_cancel (mul_right_cancel h')))

theorem root_scalars_diagonal
    (c : ∀ (i j : Fin 3), i ≠ j → Fˣ)
    (hc : ∀ (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      c i j hij * c j k hjk = c i k hik) :
    ∃ d : Fin 3 → Fˣ, ∀ (i j : Fin 3) (hij : i ≠ j),
      c i j hij = d i * (d j)⁻¹ := by
  let d : Fin 3 → Fˣ := ![c 0 2 (by decide), c 1 2 (by decide), 1]
  refine ⟨d, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  · exact (eq_mul_inv_iff_mul_eq).mpr (hc 0 1 2 (by decide) (by decide) (by decide))
  · simp [d]
  · exact (eq_mul_inv_iff_mul_eq).mpr (hc 1 0 2 (by decide) (by decide) (by decide))
  · simp [d]
  · have h := hc 1 2 0 (by decide) (by decide) (by decide)
    have h' := hc 1 0 2 (by decide) (by decide) (by decide)
    change c 2 0 _ = 1 * (c 0 2 _)⁻¹
    rw [one_mul, eq_inv_iff_mul_eq_one]
    apply mul_left_cancel (a := c 1 2 (by decide))
    rw [← mul_assoc, h, h', mul_one]
  · have h := hc 0 2 1 (by decide) (by decide) (by decide)
    have h' := hc 0 1 2 (by decide) (by decide) (by decide)
    change c 2 1 _ = 1 * (c 1 2 _)⁻¹
    rw [one_mul, eq_inv_iff_mul_eq_one]
    apply mul_left_cancel (a := c 0 2 (by decide))
    rw [← mul_assoc, h, h', mul_one]

/-- A root-preserving automorphism over a prime field is induced by a diagonal matrix. -/
theorem eq_linearConj_of_preservesRootGroups [Finite F] {p : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p)
    (α : MulAut PSL(3,F)) (hα : PreservesRootGroups α) :
    ∃ d : Fin 3 → Fˣ, α = linearConj F (diagonalGL d) := by
  choose c hc using fun i j hij => exists_root_scalar α hα (i := i) (j := j) hij
  obtain ⟨d, hd⟩ := root_scalars_diagonal c
    (fun _ _ _ hij hjk hik => root_scalar_chain α c hc hij hjk hik)
  refine ⟨d, ?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply hom_ext
  intro i j hij a
  change α (rootElement hij a) = linearConj F (diagonalGL d) (rootElement hij a)
  rw [map_rootElement_of_one hp hF α hij _ (hc i j hij),
    linearConj_diagonalGL_rootElement, hd i j hij, Units.val_mul, mul_assoc]

/-- Root-preserving automorphisms over a prime field belong to the concrete
standard subgroup. This does not assert that arbitrary automorphisms preserve roots. -/
theorem mem_standard_of_preservesRootGroups [Finite F] {p : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p)
    (α : MulAut PSL(3,F)) (hα : PreservesRootGroups α) : α ∈ standard F := by
  obtain ⟨d, rfl⟩ := eq_linearConj_of_preservesRootGroups hp hF α hα
  exact linearConj_mem_standard F _

end Matrix.PSL3.OuterSolvable.OddPrimeCoverage
