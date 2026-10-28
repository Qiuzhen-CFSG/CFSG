module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Frame

/-!
# Recovering the norm from a checked Krylov frame

Let P be the sum of the first twenty-three powers of the generator product.
The frame transitions identify each frame row with a seed acted on by a power.
Agreement of P and the proposed norm on the eleven seeds, together with
commutation with the generator product, then gives agreement on every frame
row. A checked left inverse cancels the frame. Closure under sums and products
puts P, hence the literal norm, in the given algebra.

This is a conditional certificate reduction, not yet `norm_mem`. The frame
identities and the two norm compatibility identities remain explicit. Source
and the literal candidate data are documented in `Frame.lean`.
-/

public section
open Matrix
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm

/-- The finite frame and compatibility identities suffice for the literal norm. -/
theorem norm_mem_of_frame
    (hproduct : generatorProduct = matrix252 0 * matrix252 1)
    (hstep : ∀ (s : Fin 11) (t : Fin 22),
      vecMul (orbitRow s t.val) generatorProduct = orbitRow s (t.val + 1))
    (hinverse : frameInverse * frame = 1)
    (hseed : ∀ s : Fin 11, vecMul (orbitRow s 0) normMatrix =
      ∑ t : Fin 23, orbitRow s t.val)
    (hcomm : generatorProduct * normMatrix = normMatrix * generatorProduct)
    (Q : Subalgebra (ZMod 2) (Mat 252))
    (hA : ∀ j : Fin 2, matrix252 j ∈ Q) : matrix (n := 252) c19 ∈ Q := by
  let G := generatorProduct
  let N := normMatrix
  let P : Mat 252 := ∑ t : Fin 23, G ^ t.val
  have hpowers : ∀ (s : Fin 11) (t : ℕ), t < 23 →
      vecMul (orbitRow s 0) (G ^ t) = orbitRow s t := by
    intro s t
    induction t with
    | zero => intro _; simp only [pow_zero, vecMul_one]
    | succ t ih =>
      intro ht
      rw [pow_succ, ← vecMul_vecMul, ih (by omega)]
      exact hstep s ⟨t, by omega⟩
  have hGP : G * P = P * G := by
    change G * (∑ t : Fin 23, G ^ t.val) = (∑ t : Fin 23, G ^ t.val) * G
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    exact (pow_succ' G t.val).symm.trans (pow_succ G t.val)
  have hseeds : ∀ s : Fin 11, vecMul (orbitRow s 0) P = vecMul (orbitRow s 0) N := by
    intro s
    change vecMul (orbitRow s 0) (∑ t : Fin 23, G ^ t.val) = _
    rw [vecMul_sum]
    calc
      (∑ t : Fin 23, vecMul (orbitRow s 0) (G ^ t.val)) =
          ∑ t : Fin 23, orbitRow s t.val :=
        Finset.sum_congr rfl (fun t _ => hpowers s t.val t.isLt)
      _ = vecMul (orbitRow s 0) N := (hseed s).symm
  have hrows : ∀ (s : Fin 11) (t : ℕ), t < 23 →
      vecMul (orbitRow s t) P = vecMul (orbitRow s t) N := by
    intro s t
    induction t with
    | zero => intro _; exact hseeds s
    | succ t ih =>
      intro ht
      rw [← hstep s ⟨t, by omega⟩]
      rw [vecMul_vecMul, hGP, ← vecMul_vecMul, ih (by omega),
        vecMul_vecMul, ← hcomm, ← vecMul_vecMul]
  have hframe : frame * P = frame * N := by
    funext i
    change vecMul (frame i) P = vecMul (frame i) N
    rw [frame_row]
    exact hrows (seedIndex i) (i.val % 23) (Nat.mod_lt _ (by decide))
  have he : P = N := by
    have h := congrArg (fun M : Mat 252 => frameInverse * M) hframe
    simpa only [← mul_assoc, hinverse, one_mul] using h
  have hG : G ∈ Q := by
    rw [show G = matrix252 0 * matrix252 1 from hproduct]
    exact Q.mul_mem (hA 0) (hA 1)
  have hP : P ∈ Q := Q.sum_mem (fun t _ => Q.pow_mem hG t.val)
  change N ∈ Q
  rw [← he]
  exact hP

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm
