module

public import Theory.AlgebraicGroup.BNPair.SimpleLiftCoverage
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.FinCases

/-!
Local two-cell exchange from homomorphisms out of the actual matrix group
`SL₂(k)`. The chosen reflection is `[[0,1],[-1,0]]`. Its square is diagonal,
and Gaussian elimination factors its product with a nonzero upper-root element
as upper times diagonal times lower. These identities survive any group
homomorphism, including a central isogeny onto an ambient rank-one subgroup.

For a family of such homomorphisms, isolate the simple-root factor of a Borel
element. The sign of its normalizer conjugate then determines which of the two
cells contains the product. Borel factorization and the sign alternative remain
explicit geometric premises; neither global coverage nor a Tits system is used.

Sources: GLS3, Definition 1.11.1(d), Theorem 1.11.3; Borel, §14.15 T3
(the reference there is §14.12(v), absent from the local transcription).
-/

open Matrix
open scoped MatrixGroups

namespace Theory.AlgebraicGroup.BruhatGeneration.SL2

variable {k X : Type*} [Field k] [Group X]

/-- The upper elementary root matrix. -/
@[expose] public def upper (t : k) : SL(2, k) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t

/-- The lower elementary root matrix. -/
@[expose] public def lower (t : k) : SL(2, k) :=
  SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero t

/-- A representative of the nontrivial Weyl element of `SL₂`. -/
@[expose] public def reflection : SL(2, k) :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

@[simp] public theorem upper_zero : upper (0 : k) = 1 :=
  SpecialLinearGroup.transvection_coeff_zero _

/-- A reflection lift squares to a diagonal torus element in every characteristic. -/
public theorem reflection_square : reflection (k := k) * reflection =
    SpecialLinearGroup.diag2 (-1) (neg_ne_zero.mpr one_ne_zero) := by
  apply Subtype.ext
  change !![(0 : k), 1; -1, 0] * !![0, 1; -1, 0] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.diag2_coe',
      mul_apply, Fin.sum_univ_two]

/-- The nonzero-parameter rank-one exchange identity. -/
public theorem reflection_upper {t : k} (ht : t ≠ 0) :
    reflection * upper t =
      upper (-t⁻¹) *
        SpecialLinearGroup.diag2 (-t⁻¹) (neg_ne_zero.mpr (inv_ne_zero ht)) *
          lower t⁻¹ := by
  apply Subtype.ext
  change !![(0 : k), 1; -1, 0] * (upper t).val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, upper, lower,
      SpecialLinearGroup.transvection_coe,
      SpecialLinearGroup.diag2_coe', mul_apply, Fin.sum_univ_two, ht]

/-- Simple-root factorization and root-sign transport imply two-cell exchange. -/
public theorem exchange (B T N : Subgroup X) (hTB : T ≤ B)
    {I : Type*} (φ : I → SL(2, k) →* X)
    (hupper : ∀ i t, φ i (upper t) ∈ B)
    (hdiag : ∀ i t (ht : t ≠ 0), φ i (SpecialLinearGroup.diag2 t ht) ∈ T)
    (hfactor : ∀ i b, b ∈ B → ∃ b₀ t,
      b₀ ∈ B ∧ φ i reflection * b₀ * (φ i reflection)⁻¹ ∈ B ∧
        b = b₀ * φ i (upper t))
    (hsign : ∀ i n, n ∈ N →
      (∀ t, n⁻¹ * φ i (upper t) * n ∈ B) ∨
      (∀ t, n⁻¹ * φ i (lower t) * n ∈ B)) :
    SimpleLiftExchange B N (Set.range fun i => φ i reflection) := by
  rintro s ⟨i, rfl⟩ b hb n hn
  obtain ⟨b₀, t, _hb₀, hconj, rfl⟩ := hfactor i b hb
  let a₀ := φ i reflection * b₀ * (φ i reflection)⁻¹
  have hrewrite : φ i reflection * (b₀ * φ i (upper t)) * n =
      a₀ * (φ i reflection * φ i (upper t) * n) := by
    dsimp [a₀]
    group
  rw [hrewrite]
  by_cases ht : t = 0
  · subst t
    refine ⟨a₀, 1, hconj, B.one_mem, Or.inl ?_⟩
    simp only [upper_zero, map_one, mul_one]
  · rcases hsign i n hn with hpos | hneg
    · refine ⟨a₀, n⁻¹ * φ i (upper t) * n, hconj, hpos t, Or.inl ?_⟩
      group
    · let a₁ := φ i (upper (-t⁻¹)) *
          φ i (SpecialLinearGroup.diag2 (-t⁻¹) (neg_ne_zero.mpr (inv_ne_zero ht)))
      have ha₁ : a₁ ∈ B := B.mul_mem (hupper i _) (hTB (hdiag i _ _))
      have he : φ i reflection * φ i (upper t) = a₁ * φ i (lower t⁻¹) := by
        simpa only [map_mul] using congrArg (φ i) (reflection_upper ht)
      refine ⟨a₀ * a₁, n⁻¹ * φ i (lower t⁻¹) * n,
        B.mul_mem hconj ha₁, hneg t⁻¹, Or.inr ?_⟩
      rw [he]
      group

end Theory.AlgebraicGroup.BruhatGeneration.SL2
