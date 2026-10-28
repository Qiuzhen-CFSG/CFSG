module
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
/-!
# Trace obstructions for binary two-dimensional pair blocks

Trace of a squared two-by-two matrix in characteristic two is the square
of its trace. A nonzero trace therefore forbids two-power order. For the
explicit product of two opposite transvection pairs, the trace of its cube
is (ts)²(ts+1)⁴; ts distinct from zero and one thus forbids sixth power one.
These elementary identities supply the Sp₄ involution-pair obstruction in
Aschbacher–Smith 13.5.21, printed p.924.
-/
public section
open Matrix
open scoped CharTwo
set_option linter.unusedSimpArgs false
namespace Matrix.BinaryTwoTrace
variable {F:Type*} [Field F] [CharP F 2]
private theorem trace_square (A:Matrix (Fin 2) (Fin 2) F) :
    trace (A^2)=(trace A)^2 := by
  simp only [trace_fin_two,pow_two,Matrix.mul_apply,Fin.sum_univ_two]
  ring_nf
  simp
  try ring_nf
  try simp

theorem trace_pow_two (A:Matrix (Fin 2) (Fin 2) F) (n:ℕ) :
    trace (A^(2^n))=(trace A)^(2^n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,pow_mul,trace_square,ih,pow_mul]

theorem not_pow_two (A:Matrix (Fin 2) (Fin 2) F) (ht:trace A≠0) (n:ℕ) :
    A^(2^n)≠1 := by
  intro he
  have hh := trace_pow_two A n
  rw [he] at hh
  have hz : trace (1:Matrix (Fin 2) (Fin 2) F)=0 := by simp [trace_fin_two]
  exact pow_ne_zero _ ht (hh.symm.trans hz)

@[expose] def pairBlock (t s:F) : Matrix (Fin 2) (Fin 2) F :=
  !![1+t*s+(t*s)^2,t^2*s;t*s^2,1+t*s]

theorem pairBlock_trace (t s:F) : trace (pairBlock t s)=(t*s)^2 := by
  simp [pairBlock,trace_fin_two]
  ring_nf
  simp
  try ring_nf
  try simp

theorem pairBlock_cube_trace (t s:F) : trace ((pairBlock t s)^3)=(t*s)^2*((t*s)+1)^4 := by
  simp only [pow_succ,pow_zero,mul_one,trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
    pairBlock,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring_nf
  simp
  try ring_nf
  try simp

theorem pairBlock_not_six (t s:F) (h0:t*s≠0) (h1:t*s≠1) :
    pairBlock t s^6≠1 := by
  have hz : (t*s)+1≠0 := by
    intro hh
    have he : t*s=1 := by
      have := eq_neg_of_add_eq_zero_left hh
      simpa using this
    exact h1 he
  have ht : trace ((pairBlock t s)^3)≠0 := by
    rw [pairBlock_cube_trace]
    exact mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ hz)
  have hh := not_pow_two ((pairBlock t s)^3) ht 1
  simpa only [pow_one,←pow_mul] using hh
end Matrix.BinaryTwoTrace
