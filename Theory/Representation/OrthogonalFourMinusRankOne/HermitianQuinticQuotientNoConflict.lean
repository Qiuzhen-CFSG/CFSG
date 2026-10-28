module

public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors
public import Theory.Representation.OrthogonalFourMinusRankOne.CartanFixed
public import Theory.Representation.NonsplitFour
import Mathlib.Tactic

/-!
# Quintic movement in quotients of the full binary Hermitian eight-space

A binary submodule invariant under the actual upper unipotents and a diagonal
quintic actor is contained in the upper fixed line if the actor moves its
quotient. Thus such a quotient has dimension at least six. The proof retains
the full Hermitian action, including both diagonal coordinates.
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.RankOne.QuinticAdapter
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.HermitianEquiv
open Representation.OrthogonalFourMinus.CartanFixed
open Representation.BinaryOffender Matrix.SpecialLinearGroup Subgroup

local instance quinticAdapterFixedAlgebra : Algebra (ZMod 2) (fixedField 2) := ZMod.algebra _ 2
local instance quinticAdapterBinaryModule : Module (ZMod 2) (Space 2) :=
  Module.compHom (Space 2) (algebraMap (ZMod 2) (fixedField 2))

private def scalarRepresentation : Representation (ZMod 2) (Field 2)ˣ (Field 2) where
  toFun a := (AddMonoidHom.mulLeft (a : Field 2)).toZModLinearMap 2
  map_one' := by ext x; exact one_mul x
  map_mul' a b := by ext x; exact mul_assoc (a : Field 2) (b : Field 2) x

private theorem scalar_invariant_eq_bot_or_top (a : (Field 2)ˣ)
    (ha : orderOf a = 5) (P : Submodule (ZMod 2) (Field 2))
    (hP : ∀ x ∈ P, (a : Field 2) * x ∈ P) : P = ⊥ ∨ P = ⊤ := by
  classical
  let A := zpowers a
  let : Fintype A := Fintype.ofFinite A
  have hdim : Module.finrank (ZMod 2) (Field 2) = 4 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Field 2)
    rw [Nat.card_zmod, GaloisField.card 2 4 (by decide)] at hc
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc.symm
  have hf : Function.Injective (scalarRepresentation.comp A.subtype) := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    have he := congrArg (fun f : Module.End (ZMod 2) (Field 2) => f 1) hxy
    simpa [scalarRepresentation] using he
  apply invariant_eq_bot_or_top_of_prime_card_dvd_sq_add_one
    5 (by decide) (by decide) (show Nat.card A = 5 by rw [Nat.card_zpowers, ha])
    (scalarRepresentation.comp A.subtype) hf hdim (by decide) (by decide) (by decide) P
  intro b x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp b.property)
  change (b.val : Field 2) * x ∈ P
  rw [← hi]
  have hpow (j : ℕ) : ((a ^ j : (Field 2)ˣ) : Field 2) * x ∈ P := by
    induction j with
    | zero => simpa using hx
    | succ j ih => simpa [pow_succ', mul_assoc] using hP _ ih
  exact hpow i

private theorem quintic_conjugation (a : (Field 2)ˣ) (ha : a ^ 5 = 1) :
    conjugation 2 (a : Field 2) = (a : Field 2)⁻¹ := by
  have hp : (a : Field 2) ^ 5 = 1 := congrArg Units.val ha
  change (a : Field 2) ^ (2 ^ 2) = (a : Field 2)⁻¹
  have he : (a : Field 2)^4 * (a : Field 2) = 1 := by
    simpa only [pow_succ] using hp
  exact (mul_right_injective₀ a.ne_zero) (by simpa [mul_comm] using he)

private theorem quintic_diagonal_val (a : (Field 2)ˣ) (ha : a ^ 5 = 1)
    (X : Space 2) :
    (action 2 (CartanFixed.diagonal 2 a) X).val =
      !![X.val 0 0, (a : Field 2)^2 * X.val 0 1;
        (a : Field 2)⁻¹^2 * X.val 1 0, X.val 1 1] := by
  rw [action_apply]
  have hc := quintic_conjugation a ha
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CartanFixed.diagonal, diag2_coe', adjoint, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hc,
      a.ne_zero, pow_two, mul_assoc, mul_comm]

private theorem quintic_difference (a : (Field 2)ˣ) (ha : a ^ 5 = 1)
    (X : Space 2) :
    action 2 (CartanFixed.diagonal 2 a) X - X =
      offDiagonal 2 (((a : Field 2)^2 - 1) * X.val 0 1) := by
  apply Subtype.ext
  change (action 2 (CartanFixed.diagonal 2 a) X).val - X.val = _
  rw [quintic_diagonal_val a ha X]
  have hc := quintic_conjugation a ha
  have hx := entry_conjugate 2 X 1 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonal, coordinates_symm_val, hc, hx] <;> ring

private theorem quintic_offDiagonal (a : (Field 2)ˣ) (ha : a ^ 5 = 1)
    (z : Field 2) :
    action 2 (CartanFixed.diagonal 2 a) (offDiagonal 2 z) =
      offDiagonal 2 ((a : Field 2)^2 * z) := by
  apply Subtype.ext
  rw [quintic_diagonal_val a ha]
  have hc := quintic_conjugation a ha
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonal, coordinates_symm_val, hc]

/-- A kernel preserved by the actual upper root group and quintic diagonal actor
lies in the upper fixed line whenever that same actor moves the quotient. -/
theorem quintic_moving_kernel_le_upper_fixed
    (a : (Field 2)ˣ) (ha : orderOf a = 5)
    (W : Submodule (ZMod 2) (Space 2))
    (hU : ∀ (u : Field 2) (X : Space 2), X ∈ W →
      SL2.BinarySmall.hermitian 2 (upper 2 u) X ∈ W)
    (hD : ∀ X ∈ W, SL2.BinarySmall.hermitian 2 (CartanFixed.diagonal 2 a) X ∈ W)
    (hm : ∃ X : Space 2,
      SL2.BinarySmall.hermitian 2 (CartanFixed.diagonal 2 a) X - X ∉ W) :
    W ≤ fixedSpace (SL2.BinarySmall.hermitian 2) (upperUnipotent (Field 2)) := by
  have ha5 : a ^ 5 = 1 := ha ▸ pow_orderOf_eq_one a
  have ha2 : orderOf (a ^ 2) = 5 := by rw [orderOf_pow, ha]; norm_num
  have hne : (a : Field 2)^2 - 1 ≠ 0 := by
    intro hz
    have hunit : a ^ 2 = 1 := Units.ext (by simpa using sub_eq_zero.mp hz)
    rw [hunit, orderOf_one] at ha2
    omega
  let P := W.comap ((offDiagonal 2).toAddMonoidHom.toZModLinearMap 2)
  have hP : P = ⊥ := by
    rcases scalar_invariant_eq_bot_or_top (a ^ 2) ha2 P (by
      intro z hz
      change offDiagonal 2 ((a : Field 2)^2 * z) ∈ W
      rw [← quintic_offDiagonal a ha5]
      exact hD _ hz) with hp | hp
    · exact hp
    · exfalso
      obtain ⟨X, hX⟩ := hm
      apply (hX : action 2 (CartanFixed.diagonal 2 a) X - X ∉ W)
      change action 2 (CartanFixed.diagonal 2 a) X - X ∈ W
      rw [quintic_difference a ha5]
      have hz : ((a : Field 2)^2 - 1) * X.val 0 1 ∈ P := by rw [hp]; trivial
      exact hz
  have hzero (X : Space 2) (hX : X ∈ W) : X.val 0 1 = 0 := by
    have hd : action 2 (CartanFixed.diagonal 2 a) X - X ∈ W := W.sub_mem (hD X hX) hX
    rw [quintic_difference a ha5] at hd
    have hz : ((a : Field 2)^2 - 1) * X.val 0 1 ∈ P := hd
    rw [hP, Submodule.mem_bot] at hz
    exact (mul_eq_zero.mp hz).resolve_left hne
  intro X hX
  apply (mem_fixedSpace_upper_iff 2 X).mpr
  refine ⟨?_, hzero X hX⟩
  have hd : rootDifference 2 1 X ∈ W := W.sub_mem (hU 1 X hX) hX
  have hz := hzero (rootDifference 2 1 X) hd
  rw [rootDifference_val] at hz
  simpa using hz

/-- A quotient of the full eight-dimensional Hermitian module on which the
specified quintic actor still moves has binary dimension at least six. -/
theorem six_le_finrank_quintic_moving_quotient
    (a : (Field 2)ˣ) (ha : orderOf a = 5)
    (W : Submodule (ZMod 2) (Space 2))
    (hU : ∀ (u : Field 2) (X : Space 2), X ∈ W →
      SL2.BinarySmall.hermitian 2 (upper 2 u) X ∈ W)
    (hD : ∀ X ∈ W, SL2.BinarySmall.hermitian 2 (CartanFixed.diagonal 2 a) X ∈ W)
    (hm : ∃ X : Space 2,
      SL2.BinarySmall.hermitian 2 (CartanFixed.diagonal 2 a) X - X ∉ W) :
    6 ≤ Module.finrank (ZMod 2) ((Space 2) ⧸ W) := by
  have hle := Submodule.finrank_mono (quintic_moving_kernel_le_upper_fixed a ha W hU hD hm)
  rw [upper_fixed_finrank] at hle
  have hsum := W.finrank_quotient_add_finrank
  rw [space_binary_finrank] at hsum
  omega

/-- The same actual moving quotient has at least sixty-four vectors. -/
theorem sixtyFour_le_card_quintic_moving_quotient
    (a : (Field 2)ˣ) (ha : orderOf a = 5)
    (W : Submodule (ZMod 2) (Space 2))
    (hU : ∀ (u : Field 2) (X : Space 2), X ∈ W →
      SL2.BinarySmall.hermitian 2 (upper 2 u) X ∈ W)
    (hD : ∀ X ∈ W, SL2.BinarySmall.hermitian 2 (CartanFixed.diagonal 2 a) X ∈ W)
    (hm : ∃ X : Space 2,
      SL2.BinarySmall.hermitian 2 (CartanFixed.diagonal 2 a) X - X ∉ W) :
    64 ≤ Nat.card ((Space 2) ⧸ W) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (six_le_finrank_quintic_moving_quotient a ha W hU hD hm)

end Representation.OrthogonalFourMinus.RankOne.QuinticAdapter
