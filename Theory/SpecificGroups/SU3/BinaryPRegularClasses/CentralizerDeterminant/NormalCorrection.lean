module

public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant.Adjoint
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Recovering the prescribed determinant after adjoint correction

For a normal linear centralizer witness of norm-one determinant `d`, division
by its adjoint produces a unitary centralizer element of determinant `d²`.
A power inverts squaring in the multiplicative group of the binary field.
This works even when cubing is not surjective, in particular for the cubic
center of SU₃ at odd exponents.

The normal linear witness is an explicit input, not an established consequence
of odd order here. The source-class application is GLS III 2.8.2 and 2.8.6(a),
with the SU₃ family in 2.8.10(c), `refs/KGroup/GLS3/chapter2.tex`.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant
variable {F : Type*} [Field F] {n : ℕ}

/-- A normal linear centralizer witness of norm-one determinant gives a unitary
witness with the same determinant, including when cubing is not surjective. -/
public theorem exists_unitary_commuting_det_of_normal [Finite F]
    (J : HermitianForm n F) (g : J.unitarySubgroup) (s : ℕ) (hs : 0 < s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (d : Fˣ)
    (hd : J.conj (d : F) * (d : F) = 1)
    (A : GL (Fin n) F) (hAg : Commute A g.val)
    (hAn : Commute A (adjoint J A)) (hAd : GeneralLinearGroup.det A = d) :
    ∃ C : J.unitarySubgroup, Commute C.val g.val ∧ GeneralLinearGroup.det C.val = d := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let B : J.unitarySubgroup := ⟨A * (adjoint J A)⁻¹, polarRatio_mem_unitary J A hAn⟩
  have hBg : Commute B.val g.val := hAg.mul_left (commute_adjoint J g A hAg).inv_left
  have hdi : (J.conj (d : F))⁻¹ = (d : F) := by
    exact inv_eq_of_mul_eq_one_right hd
  have hBd : (GeneralLinearGroup.det B.val : F) = (d : F) ^ 2 := by
    change (GeneralLinearGroup.det (A * (adjoint J A)⁻¹) : F) = _
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      det_adjoint, hAd, hdi, pow_two]
  let k := 2 ^ (s * 2 - 1)
  have hk : 2 * k = (2 ^ s) ^ 2 := by
    dsimp only [k]
    rw [← pow_succ', Nat.sub_add_cancel (by omega), pow_mul]
  refine ⟨B ^ k, hBg.pow_left k, ?_⟩
  apply Units.ext
  change (GeneralLinearGroup.det (B.val ^ k) : F) = (d : F)
  rw [map_pow, Units.val_pow_eq_pow_val, hBd, ← pow_mul, hk, ← hcard,
    Nat.card_eq_fintype_card, FiniteField.pow_card]

end Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant
