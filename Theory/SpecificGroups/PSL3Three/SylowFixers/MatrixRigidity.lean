module

public import Theory.SpecificGroups.PSL3Three.Generators

/-!
# A matrix rigidity calculation for pointwise Sylow fixers of PSL₃(3)

The matrices a and b generate a semidihedral two-group, and adjoining the
coordinate cycle r generates SL₃(3). An automorphism fixing a and b sends r
to a matrix y with y³ = 1 and (a y² b)² = (a² y b y)³ = 1. The first two
relations give y² = d y d, where d = a⁻¹b. Its nine scalar equations have
at most the twelve displayed solutions over F₃. The remaining relations
leave r and its conjugate by a⁴. Both finite checks reduce in Lean's kernel.

Only this marked generator calculation is needed; no classification of the
full automorphism group is used. Source: Aschbacher–Smith, E.6.8(5), printed
p.248, and the PSL₃(3) model in 1.1.5(3)(e), printed p.502.
-/

@[expose] public section

namespace Matrix.PSL3Three.SylowFixers

def a : SL := ⟨!![2, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩
def b : SL := ⟨!![2, 0, 0; 0, 1, 0; 0, 1, 2], by decide⟩
def r : SL := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩
def r' : SL := ⟨!![0, 0, 2; 2, 0, 0; 0, 1, 0], by decide⟩

def d : SL := ⟨!![1, 0, 0; 0, 0, 2; 0, 1, 0], by decide⟩


private def candidate : Fin 12 → Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ![!![0, 0, 0; 0, 0, 0; 0, 0, 0],
    !![0, 0, 0; 0, 2, 0; 0, 0, 2],
    !![0, 0, 1; 1, 0, 0; 0, 1, 0],
    !![0, 0, 2; 2, 0, 0; 0, 1, 0],
    !![0, 1, 0; 0, 0, 2; 2, 0, 0],
    !![0, 1, 1; 2, 2, 1; 1, 2, 1],
    !![0, 1, 2; 1, 1, 1; 1, 2, 2],
    !![0, 2, 0; 0, 0, 2; 1, 0, 0],
    !![0, 2, 1; 2, 1, 1; 2, 2, 2],
    !![0, 2, 2; 1, 2, 1; 2, 2, 1],
    !![1, 0, 0; 0, 0, 0; 0, 0, 0],
    !![1, 0, 0; 0, 2, 0; 0, 0, 2]]

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
private theorem quadratic_certificate : ∀ x00 x01 x02 x10 x11 x12 x20 x21 x22 : ZMod 3,
    x00 * x00 + x01 * x10 + x02 * x20 = x00 →
    x00 * x01 + x01 * x11 + x02 * x21 = x02 →
    x00 * x02 + x01 * x12 + x02 * x22 = 2 * x01 →
    x10 * x00 + x11 * x10 + x12 * x20 = 2 * x20 →
    x10 * x01 + x11 * x11 + x12 * x21 = 2 * x22 →
    x10 * x02 + x11 * x12 + x12 * x22 = x21 →
    x20 * x00 + x21 * x10 + x22 * x20 = x10 →
    x20 * x01 + x21 * x11 + x22 * x21 = x12 →
    x20 * x02 + x21 * x12 + x22 * x22 = 2 * x11 →
    ∃ j : Fin 12, x00 = candidate j 0 0 ∧ x01 = candidate j 0 1 ∧ x02 = candidate j 0 2 ∧ x10 = candidate j 1 0 ∧ x11 = candidate j 1 1 ∧ x12 = candidate j 1 2 ∧ x20 = candidate j 2 0 ∧ x21 = candidate j 2 1 ∧ x22 = candidate j 2 2 := by
  decide +kernel

private theorem quadratic_candidates (y : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hy : y ^ 2 = d.val * y * d.val) : ∃ j : Fin 12, y = candidate j := by
  have h00 := congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m 0 0) hy
  have h01 := congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m 0 1) hy
  have h02 := congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m 0 2) hy
  have h10 := congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m 1 0) hy
  have h11 := congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m 1 1) hy
  have h12 := congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m 1 2) hy
  have h20 := congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m 2 0) hy
  have h21 := congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m 2 1) hy
  have h22 := congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m 2 2) hy
  norm_num only [pow_two, d, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.tail_cons, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, mul_one] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  obtain ⟨j, h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := quadratic_certificate (y 0 0) (y 0 1) (y 0 2) (y 1 0) (y 1 1) (y 1 2) (y 2 0) (y 2 1) (y 2 2)
    h00 h01 (h02.trans (mul_comm _ _)) h10 h11
    (h12.trans (by
      calc
        2 * y 2 1 * 2 = ((2 : ZMod 3) * 2) * y 2 1 := by ring
        _ = y 2 1 := by rw [show (2 : ZMod 3) * 2 = 1 by decide, one_mul]))
    h20 h21 (h22.trans (mul_comm _ _))
  refine ⟨j, ?_⟩
  ext i k
  fin_cases i <;> fin_cases k <;> assumption

set_option maxRecDepth 10000 in
private theorem candidates_rigidity : ∀ j : Fin 12,
    candidate j ^ 3 = 1 → (a.val ^ 2 * candidate j * b.val * candidate j) ^ 3 = 1 →
    candidate j = r.val ∨ candidate j = r'.val := by
  decide +kernel

theorem matrix_rigidity (y : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hq : y ^ 2 = d.val * y * d.val) (h3 : y ^ 3 = 1)
    (hw : (a.val ^ 2 * y * b.val * y) ^ 3 = 1) : y = r.val ∨ y = r'.val := by
  obtain ⟨j, rfl⟩ := quadratic_candidates y hq
  exact candidates_rigidity j h3 hw
end Matrix.PSL3Three.SylowFixers
