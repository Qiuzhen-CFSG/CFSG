module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Odd Order Matrix Trace

Two matrices with the same odd finite-order bound and the same residue
over a local ring have equal traces when two is a nonunit. The recursive
geometric sum intertwines the matrices. Its reduction is a power of their
common invertible residue matrix, so its determinant is a unit in the local
ring and the matrices are conjugate. No completeness, Noetherian, domain,
or characteristic-zero hypothesis is needed.

This supplies the rigidity step in the elementary Nagao trace argument.
The recursive intertwiner is exposed because its defining equations are
part of the finite-sum interface.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/NagaoTrace.lean` (revision `c3503435`).
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Module

namespace ModularBlock.NagaoTrace

universe u v

attribute [local instance] Fintype.ofFinite

/-- The noncommutative geometric sum used to conjugate two finite-order
elements with the same residue. -/
def intertwinerSum {S : Type*} [Semiring S] (P Q : S) : ℕ → S
  | 0 => 0
  | n + 1 => P ^ n + intertwinerSum P Q n * Q

lemma mul_intertwinerSum_add_pow {S : Type*} [Semiring S]
    (P Q : S) (n : ℕ) :
    P * intertwinerSum P Q n + Q ^ n =
      P ^ n + intertwinerSum P Q n * Q := by
  induction n with
  | zero => simp [intertwinerSum]
  | succ n ih =>
    calc
      P * intertwinerSum P Q (n + 1) + Q ^ (n + 1) =
          P ^ (n + 1) + (P * intertwinerSum P Q n + Q ^ n) * Q := by
            simp only [intertwinerSum, mul_add, pow_succ]
            have hpcomm : P * P ^ n = P ^ n * P := by
              rw [← pow_succ', ← pow_succ]
            rw [hpcomm]
            rw [add_mul, mul_assoc, add_assoc]
      _ = P ^ (n + 1) +
          (P ^ n + intertwinerSum P Q n * Q) * Q := by rw [ih]
      _ = P ^ (n + 1) + intertwinerSum P Q (n + 1) * Q := by
        rw [intertwinerSum]

lemma map_intertwinerSum {S T : Type*} [Semiring S] [Semiring T]
    (f : S →+* T) (P Q : S) (n : ℕ) :
    f (intertwinerSum P Q n) = intertwinerSum (f P) (f Q) n := by
  induction n with
  | zero => simp [intertwinerSum]
  | succ n ih => simp [intertwinerSum, ih]

lemma intertwinerSum_self_of_char_two {S : Type*} [Semiring S]
    (h2 : (2 : S) = 0) (P : S) {n : ℕ} (hn : Odd n) :
    intertwinerSum P P n = P ^ (n - 1) := by
  have hdouble (a : S) : a + a = 0 := by
    rw [← two_mul, h2, zero_mul]
  have hpair : ∀ k : ℕ,
      intertwinerSum P P (2 * k) = 0 ∧
        intertwinerSum P P (2 * k + 1) = P ^ (2 * k) := by
    intro k
    induction k with
    | zero => simp [intertwinerSum]
    | succ k ih =>
      have heven : intertwinerSum P P (2 * (k + 1)) = 0 := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
          intertwinerSum, ih.2, ← pow_succ, hdouble]
      refine ⟨heven, ?_⟩
      rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by rfl,
        intertwinerSum, heven, zero_mul, add_zero]
  rcases hn with ⟨k, rfl⟩
  simpa using (hpair k).2

/-- Odd-order matrix lifts with the same residue are conjugate enough to have
the same trace.  No completeness, Noetherian, domain, or characteristic-zero
hypothesis is needed. -/
theorem matrix_trace_eq_of_odd_order_of_residue_eq
    {R : Type u} {ι : Type v} [CommRing R] [IsLocalRing R]
    [Fintype ι] [DecidableEq ι]
    (h2 : ¬ IsUnit (2 : R))
    {P Q : Matrix ι ι R} {n : ℕ} (hn : Odd n)
    (hP : P ^ n = 1) (hQ : Q ^ n = 1)
    (hres : P.map (IsLocalRing.residue R) =
      Q.map (IsLocalRing.residue R)) :
    Matrix.trace P = Matrix.trace Q := by
  let S : Matrix ι ι R := intertwinerSum P Q n
  have hn0 : n ≠ 0 := by
    rcases hn with ⟨k, rfl⟩
    omega
  have hinter : P * S = S * Q := by
    have h := mul_intertwinerSum_add_pow P Q n
    dsimp [S]
    rw [hP, hQ] at h
    have h' : (1 : Matrix ι ι R) + P * intertwinerSum P Q n =
        1 + intertwinerSum P Q n * Q := by
      simpa [add_comm] using h
    exact add_left_cancel h'
  have htwo_res : IsLocalRing.residue R (2 : R) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h2
  let Pbar : Matrix ι ι (IsLocalRing.ResidueField R) :=
    P.map (IsLocalRing.residue R)
  have hPbar_pow : Pbar ^ n = 1 := by
    simpa only [Pbar, RingHom.mapMatrix_apply, Matrix.map_pow,
      map_one] using congrArg
      ((IsLocalRing.residue R).mapMatrix (m := ι)) hP
  have hPbar_unit : IsUnit Pbar :=
    IsUnit.of_pow_eq_one hPbar_pow hn0
  have hSmap : S.map (IsLocalRing.residue R) = Pbar ^ (n - 1) := by
    change (IsLocalRing.residue R).mapMatrix S = _
    rw [show (IsLocalRing.residue R).mapMatrix S =
        intertwinerSum
          ((IsLocalRing.residue R).mapMatrix P)
          ((IsLocalRing.residue R).mapMatrix Q) n by
      simpa [S] using map_intertwinerSum
        ((IsLocalRing.residue R).mapMatrix (m := ι)) P Q n]
    change intertwinerSum Pbar
      (Q.map (IsLocalRing.residue R)) n = Pbar ^ (n - 1)
    rw [← hres]
    apply intertwinerSum_self_of_char_two
    have htwoK : (2 : IsLocalRing.ResidueField R) = 0 := by
      exact (map_ofNat (IsLocalRing.residue R) 2).symm.trans htwo_res
    calc
      (2 : Matrix ι ι (IsLocalRing.ResidueField R)) =
          (2 : IsLocalRing.ResidueField R) •
            (1 : Matrix ι ι (IsLocalRing.ResidueField R)) := by
              ext i j
              simp [Matrix.ofNat_apply, Matrix.one_apply]
      _ = 0 := by rw [htwoK, zero_smul]
    exact hn
  have hSbar_unit : IsUnit (S.map (IsLocalRing.residue R)) := by
    rw [hSmap]
    exact hPbar_unit.pow _
  have hdetS_unit : IsUnit S.det := by
    apply isUnit_of_map_unit (IsLocalRing.residue R)
    rw [(IsLocalRing.residue R).map_det]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hSbar_unit
  have hS_unit : IsUnit S :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hdetS_unit
  let U : (Matrix ι ι R)ˣ := hS_unit.unit
  have hU : (U : Matrix ι ι R) = S := hS_unit.unit_spec
  have hconj :
      (↑U⁻¹ : Matrix ι ι R) * P * (U : Matrix ι ι R) = Q := by
    rw [hU]
    calc
      (↑U⁻¹ : Matrix ι ι R) * P * S =
          (↑U⁻¹ : Matrix ι ι R) * (P * S) := by
            rw [Matrix.mul_assoc]
      _ = (↑U⁻¹ : Matrix ι ι R) * (S * Q) := by rw [hinter]
      _ = (↑U⁻¹ : Matrix ι ι R) * ((U : Matrix ι ι R) * Q) := by rw [hU]
      _ = Q := by rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  calc
    Matrix.trace P =
        Matrix.trace ((↑U⁻¹ : Matrix ι ι R) * P * (U : Matrix ι ι R)) :=
      (Matrix.trace_units_conj' U P).symm
    _ = Matrix.trace Q := by rw [hconj]

end ModularBlock.NagaoTrace
