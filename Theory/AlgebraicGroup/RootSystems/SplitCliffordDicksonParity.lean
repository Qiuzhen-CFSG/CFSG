module

public import Theory.AlgebraicGroup.RootSystems.CliffordSplitOddCentralizer
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Dickson parity for split Clifford implementers

Let `Q` be a finite-dimensional split quadratic form of positive hyperbolic
rank.  This module proves that if an even Clifford unit and a unit in
Mathlib's `lipschitzGroup Q` induce the same ordinary conjugation on every
embedded vector, then their quotient is even.  This is the parity input for
the characteristic-free split Clifford normalizer factorization.

The proof uses the word parity built into Mathlib's exact definition of the
Lipschitz group, rather than a determinant.  An invertible embedded vector is
odd, and its inverse is odd as well: invertibility forces its quadratic value
to be nonzero, after which the inverse is the corresponding scalar multiple
of the vector.  Induction on `Subgroup.closure` therefore assigns every
Lipschitz word a common `ZMod 2` degree for the word and its inverse.  This
works unchanged in characteristic two and requires no `Invertible (2 : k)`.

For implementers `a` and `b`, equality of conjugations makes `b⁻¹ * a`
commute with all Clifford vectors.  Its degree is the word degree of `b`.
The odd alternative is impossible by the split odd-centralizer theorem from
`CliffordSplitOddCentralizer`, since `b⁻¹ * a` is a unit.  Hence `b` and
`b⁻¹` are even, and the requested quotient `a * b⁻¹` is even.  Algebraic
closure is retained in the public statement to match the split orthogonal
factorization consumer, although the word-parity argument itself uses only
the field and split-form hypotheses.
-/

open CliffordAlgebra

universe u

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

private theorem cliffordGenerator_evenOdd_certificate
    (s : SplitQuadraticForm Q) (x : (CliffordAlgebra Q)ˣ)
    (hx : (x : CliffordAlgebra Q) ∈ Set.range (CliffordAlgebra.ι Q)) :
    (x : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q 1 ∧
      (↑(x⁻¹) : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q 1 := by
  let _ : Nontrivial (CliffordAlgebra Q) :=
    s.cliffordToExterior.symm.injective.nontrivial
  obtain ⟨v, hv⟩ := hx
  have hxOdd : (x : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q 1 := by
    rw [← hv]
    exact CliffordAlgebra.ι_mem_evenOdd_one Q v
  have hQv : Q v ≠ 0 := by
    intro hQv
    have hsquare : (x : CliffordAlgebra Q) * x = 0 := by
      rw [← hv, CliffordAlgebra.ι_sq_scalar, hQv, map_zero]
    have hxzero : (x : CliffordAlgebra Q) = 0 := by
      calc
        (x : CliffordAlgebra Q) =
            ((↑(x⁻¹) : CliffordAlgebra Q) * x) * x := by simp
        _ = (↑(x⁻¹) : CliffordAlgebra Q) * (x * x) := by
          rw [mul_assoc]
        _ = 0 := by rw [hsquare, mul_zero]
    exact Units.ne_zero x hxzero
  let _ : Invertible (Q v) := invertibleOfNonzero hQv
  have hxInv : (↑(x⁻¹) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q (⅟(Q v) • v) := by
    apply (Units.isUnit x).mul_left_cancel
    rw [Units.mul_inv]
    rw [← hv, map_smul, mul_smul_comm,
      CliffordAlgebra.ι_sq_scalar, Algebra.smul_def, ← map_mul,
      invOf_mul_self, map_one]
  refine ⟨hxOdd, ?_⟩
  rw [hxInv]
  exact CliffordAlgebra.ι_mem_evenOdd_one Q _

private theorem lipschitz_evenOdd_certificate
    (s : SplitQuadraticForm Q) {x : (CliffordAlgebra Q)ˣ}
    (hx : x ∈ lipschitzGroup Q) :
    ∃ n : ZMod 2,
      (x : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q n ∧
        (↑(x⁻¹) : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q n := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' with
  | mem x hx =>
      obtain ⟨hx, hxInv⟩ := cliffordGenerator_evenOdd_certificate s x hx
      exact ⟨1, hx, hxInv⟩
  | inv_mem x hx =>
      obtain ⟨hx, hxInv⟩ := cliffordGenerator_evenOdd_certificate s x hx
      exact ⟨1, hxInv, by simpa using hx⟩
  | one =>
      exact ⟨0,
        SetLike.one_mem_graded (A := CliffordAlgebra.evenOdd Q),
        by simpa using
          (SetLike.one_mem_graded (A := CliffordAlgebra.evenOdd Q))⟩
  | mul x y _ _ hx hy =>
      obtain ⟨i, hx, hxInv⟩ := hx
      obtain ⟨j, hy, hyInv⟩ := hy
      refine ⟨i + j, SetLike.mul_mem_graded hx hy, ?_⟩
      simpa [add_comm] using SetLike.mul_mem_graded hyInv hxInv

/-- If an even unit and a Lipschitz unit have the same ordinary conjugation
on every vector of a positive-rank split quadratic space, their quotient is
even.  The statement is valid in characteristic two. -/
public theorem CliffordAlgebra.mul_inv_mem_even_of_mem_even_of_lipschitzGroup
    [IsAlgClosed k]
    (s : SplitQuadraticForm Q) (hpos : 0 < s.rank)
    {a b : (CliffordAlgebra Q)ˣ}
    (ha : (a : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q)
    (hb : b ∈ lipschitzGroup Q)
    (hconj : ∀ v : V,
      (a : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(a⁻¹) =
        (b : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(b⁻¹)) :
    (↑(a * b⁻¹) : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q := by
  let _ : Nontrivial (CliffordAlgebra Q) :=
    s.cliffordToExterior.symm.injective.nontrivial
  obtain ⟨n, hbGrade, hbInvGrade⟩ := lipschitz_evenOdd_certificate s hb
  have hdGrade : (↑(b⁻¹ * a) : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q n := by
    simpa using SetLike.mul_mem_graded hbInvGrade ha
  have hdComm (v : V) :
      Commute (↑(b⁻¹ * a) : CliffordAlgebra Q) (CliffordAlgebra.ι Q v) := by
    show (↑(b⁻¹ * a) : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
      CliffordAlgebra.ι Q v * (↑(b⁻¹ * a) : CliffordAlgebra Q)
    calc
      (↑(b⁻¹ * a) : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
          (↑(b⁻¹) : CliffordAlgebra Q) *
            ((a : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(a⁻¹)) *
              (a : CliffordAlgebra Q) := by simp [mul_assoc]
      _ = (↑(b⁻¹) : CliffordAlgebra Q) *
            ((b : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(b⁻¹)) *
              (a : CliffordAlgebra Q) := by rw [hconj v]
      _ = CliffordAlgebra.ι Q v *
            (↑(b⁻¹ * a) : CliffordAlgebra Q) := by simp [mul_assoc]
  by_cases hn : n = 0
  · subst n
    change (↑(a * b⁻¹) : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q 0
    simpa using SetLike.mul_mem_graded ha hbInvGrade
  · have hnOne : n = 1 := Fin.eq_one_of_ne_zero n hn
    subst n
    have hzero : (↑(b⁻¹ * a) : CliffordAlgebra Q) = 0 :=
      CliffordAlgebra.eq_zero_of_mem_odd_of_commute_ι
        s hpos _ hdGrade hdComm
    exact (Units.ne_zero (b⁻¹ * a) hzero).elim

end Theory.AlgebraicGroup
