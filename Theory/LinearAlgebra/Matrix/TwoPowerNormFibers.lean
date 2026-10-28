module

public import Theory.LinearAlgebra.Matrix.TwoPowerIdempotentFibers
public import Theory.LinearAlgebra.Matrix.TwoPowerVectorFibers

/-!
# Norm fibers of involutory matrices over two-power residue rings

For `T = I + 2 M` with `T² = I`, the doubled norm `2 (v + T v)` is
`4 (I + M) v`. Modulo `2^(n-2)`, the matrix `I + M` is idempotent.
The reduced fiber over a nonzero top two-torsion vector is counted by its
binary projection, and every reduced vector has sixteen lifts. Thus the
original fiber has size zero, sixteen, or `2^(n+2)`, as encoded by
`BinaryIdempotentPlane.weight`.

Source context: the elementary homocyclic norm calculation in the
MacWilliams–Sah bound quoted by Janko–Thompson, Math. Z. 113 (1970), 1.1,
printed p.385. The proof assembles the algebraic reduction, idempotent
lifting, and uniform reduction-fiber counts from the imported modules.
-/

public section

open Matrix
namespace TwoPowerNorm

/-- The doubled norm fiber of an involutory matrix has the weight prescribed
by the binary reduction of `I + M`. -/
theorem norm_fiber_card (n : ℕ) (hn : 3 ≤ n)
    (T M : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ n))) (hT : T ^ 2 = 1)
    (hM : T = 1 + (2 : ZMod (2 ^ n)) • M)
    (w : BinaryIdempotentPlane.Vec) (hw : w ≠ 0) (h2 : 2 ∣ 2 ^ n) :
    Nat.card {v : Fin 2 → ZMod (2 ^ n) //
      (2 : ZMod (2 ^ n)) • (v + T.mulVec v) = topVector n w} =
      BinaryIdempotentPlane.weight 16 (2 ^ (n + 2))
        (1 + M.map (ZMod.castHom h2 (ZMod 2))) w := by
  let r := ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le n 2)) (ZMod (2 ^ (n - 2)))
  have h2' : 2 ∣ 2 ^ (n - 2) := dvd_pow_self 2 (by omega)
  have heq := Nat.card_congr (Equiv.subtypeEquivRight fun v =>
    norm_eq_top_iff_reduced n hn T M hM w v)
  rw [heq, lift_count n (by omega)
    (fun u => (1 + M.map r).mulVec u = topVector (n - 2) w)]
  rw [idempotent_fiber_card (n - 2) (by omega) (1 + M.map r)
    (reduced_idempotent n (by omega) T M hT hM) w hw h2']
  rw [reduced_binary_eq n M h2 h2']
  have hpow : 16 * 2 ^ (n - 2) = 2 ^ (n + 2) := by
    rw [show 16 = 2 ^ 4 from rfl, ← pow_add]
    congr 1
    omega
  simp only [BinaryIdempotentPlane.weight_eq, mul_ite, mul_zero, mul_one, hpow]

end TwoPowerNorm
