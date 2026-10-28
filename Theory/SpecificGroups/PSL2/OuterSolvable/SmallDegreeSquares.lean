module

public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage
public import Theory.SpecificGroups.PSL2.OuterSolvable.Semilinear
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Mathlib.RingTheory.IntegralDomain

/-!
# Outer squares of odd PSL₂ in field degree at most two

The proved inner--diagonal--field factorization covers every automorphism.
Modulo inner automorphisms, squaring removes the field part in degrees
one and two. The remaining image of the field units is cyclic.
The argument uses the actual central quotient and does not lift abstract
automorphisms through SL₂.

Source: GLS3, Theorem 2.5.12(a,c,d) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace Theory.PSL2.OuterSolvable.SmallDegreeSquares
variable {F : Type*} [Field F] [Finite F]

/-- The actual diagonal action followed by Aut → Aut/Inn. -/
@[expose] def diagonalOuter : Fˣ →* MulAut.Outer (Group F) :=
  (QuotientGroup.mk' (MulAut.innerSubgroup (Group F))).comp diagonalAutHom

theorem diagonalOuter_range_isCyclic : IsCyclic (diagonalOuter (F := F)).range :=
  isCyclic_of_surjective diagonalOuter.rangeRestrict diagonalOuter.rangeRestrict_surjective

/-- Every outer square is diagonal for odd fields of degree at most two. -/
theorem outer_square_mem {p n : ℕ} (hp : p.Prime) (ho : Odd p)
    (hn : n ≤ 2) (hF : Nat.card F = p ^ n) (a : MulAut (Group F)) :
    (QuotientGroup.mk' (MulAut.innerSubgroup (Group F)) a) ^ 2 ∈
      (diagonalOuter (F := F)).range := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    have hc := FiniteField.even_card_of_char_two h
    have hodd := ho.pow (n := n)
    rw [← Nat.card_eq_fintype_card, hF] at hc
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_iff.mpr hc)
  obtain ⟨g, u, σ, ha⟩ := OddCoverage.semilinear_coverage_of_root_reductions
    (OddCoverage.exists_root_weyl_one_normalization hchar)
    (fun b hU _ h1 => OddCoverage.rootParameter_mul hchar b hU h1) a
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Group F))
  let d := diagonalOuter (F := F)
  let f := q.comp projectiveFieldAutHom
  have hσ : σ ^ 2 = 1 := FiniteField.ringAut_sq_of_card_prime_pow hp hn hF σ
  have hq : q a = d u * f σ := by
    have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    simp only [ha, map_mul, hg, one_mul]
    rfl
  have hcov : f σ * d u = d (fieldUnitsAction σ u) * f σ := by
    change q (projectiveFieldAutHom σ) * q (diagonalAutHom u) =
      q (diagonalAutHom (fieldUnitsAction σ u)) * q (projectiveFieldAutHom σ)
    rw [diagonal_field_covariance]
    simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨u * fieldUnitsAction σ u, ?_⟩
  change d (u * fieldUnitsAction σ u) = (q a) ^ 2
  rw [hq]
  symm
  calc
    (d u * f σ) ^ 2 = d u * (f σ * d u) * f σ := by simp only [pow_two, mul_assoc]
    _ = (d u * d (fieldUnitsAction σ u)) * (f σ * f σ) := by rw [hcov]; group
    _ = d (u * fieldUnitsAction σ u) := by
      rw [← pow_two, ← map_pow, hσ, map_one, mul_one, ← map_mul]

end Theory.PSL2.OuterSolvable.SmallDegreeSquares
