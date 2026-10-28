module

public import Theory.SpecificGroups.HaradaNorton.MatrixData
public import Mathlib.Algebra.BigOperators.Fin
/-!
# Packed checks for the Harada–Norton column action

Natural-number dot products are transported to `ZMod 5` by induction. A closed
Boolean check therefore certifies multiplication of a column by the actual
ATLAS matrix. Adapted from `Lyons.Atlas111Arithmetic` in this repository;
base-five data conventions are documented in `../../MatrixSources.md`.
-/

namespace HaradaNorton.OrderCertificate.IndexArithmetic
open Matrix
set_option maxRecDepth 10000

@[expose] public def packedDot : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, x, y => packedDot n x y + (x / 5 ^ n % 5) * (y / 5 ^ n % 5)

public theorem packedDot_eq (n x y : ℕ) :
    (packedDot n x y : ZMod 5) =
      ∑ j : Fin n, ((x / 5 ^ j.val : ℕ) : ZMod 5) *
        ((y / 5 ^ j.val : ℕ) : ZMod 5) := by
  induction n with
  | zero => simp [packedDot]
  | succ n ih =>
    simp only [packedDot, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod, ih,
      Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

@[expose] public def decodeVector (x : ℕ) : Fin 133 → ZMod 5 :=
  fun i => ((x / 5 ^ i.val % 5 : ℕ) : ZMod 5)

@[expose] public def checkVector (rows : Fin 133 → ℕ) (x y : ℕ) : Bool :=
  (List.finRange 133).all fun i =>
    packedDot 133 (rows i) x % 5 == y / 5 ^ i.val % 5

public theorem checkVector_sound (rows : Fin 133 → ℕ) (x y : ℕ)
    (h : checkVector rows x y = true) :
    decodeMatrix rows *ᵥ decodeVector x = decodeVector y := by
  funext i
  have hi : packedDot 133 (rows i) x % 5 = y / 5 ^ i.val % 5 := by
    exact beq_iff_eq.mp (List.all_eq_true.mp h i (List.mem_finRange i))
  change (∑ j : Fin 133, _ * _) = _
  simpa only [decodeMatrix, decodeVector, ZMod.natCast_mod, packedDot_eq] using
    congrArg (fun z : ℕ => (z : ZMod 5)) hi

end HaradaNorton.OrderCertificate.IndexArithmetic
