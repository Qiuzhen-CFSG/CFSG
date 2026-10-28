module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.CoordinateActions

/-!
# Simple-coroot reflection on the concrete Spin points

The coroot-word diagonal from `CorootPoints` and the normalizer permutation
from `CoordinateActions` give the Cartan reflection equation directly on the
natural space. Faithfulness of the characteristic-two Spin action then gives
the equation on the prescribed source words, in their original order.

Source: GLS3, Chapter 1, Theorem 1.12.1(e,i).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open PointGeneration
set_option linter.unusedSimpArgs false
universe u
variable (k : Type u) [Field k]
namespace PointGeneration
def diagonalAction (d : Fin 4 → kˣ) (z : HyperbolicSpace k 4) : HyperbolicSpace k 4 :=
  (fun p => (d p : k) * z.1 p, fun p => ((d p : k)⁻¹) * z.2 p)
set_option linter.unnecessarySeqFocus false in
theorem simpleAction_coroot_conjugation (i j : Fin 4) (t : kˣ) (z : HyperbolicSpace k 4) :
    simpleAction k i (diagonalAction k (corootDiagonal k (simpleRoot j) t)
      (simpleAction k i z)) =
      diagonalAction k (corootDiagonal k (simpleRoot j) t)
        (diagonalAction k (corootDiagonal k (simpleRoot i) (t ^ (-typeDCartanMatrix 2 j i))) z) := by
  fin_cases i <;> fin_cases j
  all_goals apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [diagonalAction, simpleAction, simpleRoot, typeDSimpleRootIndex,
      typeDCartanMatrix, corootDiagonal]
    norm_num [Fin.ext_iff, pow_two] <;> field_simp

/-- Evaluation of a hyperbolic diagonal uses precisely these scalar coordinates. -/
theorem diagonalAction_spec (d : Fin 4 → kˣ) (z : HyperbolicSpace k 4) :
    (hyperbolicDiagonalPoint 4 d).1 z = diagonalAction k d z := by
  apply Prod.ext
  · rfl
  · funext p
    exact congrArg (fun a : k => a * z.2 p) (Units.val_inv_eq_inv_val (d p))
end PointGeneration

variable [IsAlgClosed k] [CharP k 2]

/-- The Cartan reflection equation for the same source simple normalizers and coroots. -/
theorem simpleNormalizer_simpleCoroot_conjugation (i j : Fin 4) (t : kˣ) :
    (simpleNormalizer k i)⁻¹ * simpleCoroot k j t * simpleNormalizer k i =
      simpleCoroot k j t * simpleCoroot k i (t ^ (-typeDCartanMatrix 2 j i)) := by
  rw [show (simpleNormalizer k i)⁻¹ = simpleNormalizer k i from normalizerWord_inv k _ _]
  apply naturalAction_injective k
  simp only [map_mul, naturalAction_corootWord]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, simpleNormalizer_apply,
    diagonalAction_spec]
  exact simpleAction_coroot_conjugation k i j t z

end Triality.SimplyConnected.Pinning
