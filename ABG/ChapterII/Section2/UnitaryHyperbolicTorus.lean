module
public import ABG.ChapterII.Section2.UnitaryQuadraticCoordinates
public import BenderSuzuki.MatrixGroups.HermitianConjugation
public import Theory.SpecificGroups.GL2.DiagonalSwap

/-!
# The actual unitary hyperbolic torus and reflection

Over GF(p^(2n)) for odd p, the full multiplicative group of the quadratic
field embeds in the original standard GU2. An external involution acts on
this torus by a ↦ (a^(p^n))⁻¹, and every norm-one element of the torus is
the actual scalar matrix with that coefficient. The statement does not
assume a Sylow shape or a congruence restriction on p^n.

Choose z with z*conj(z)=-1. The invertible basis matrix [[1,1],[z,-z]]
transports the identity Gram matrix to twice the coordinate-swap matrix.
In this basis diag(a,conj(a)⁻¹) and coordinate swap preserve the form.
Conjugating them back gives the torus and reflection in the original GU2.
The shared GL diagonal map gives injectivity, the off-diagonal swap entry
proves externality, and swapping the two diagonal entries gives the stated
inverse-Frobenius action. For norm-one a both diagonal entries equal a;
scalar matrices are unaffected by basis conjugation.

Source: Alperin–Brauer–Gorenstein II.2 Lemma 1(i),(ii), article p.17.
This is the concrete torus input to the separate semidihedral Sylow model.
All forms, field involutions, and scalar maps are the existing definitions.
-/

open Matrix
open Matrix.GeneralLinearGroup
open scoped Matrix
open BenderSuzuki.MatrixGroups

namespace ABG
variable {F : Type*} [Field F]

private theorem exists_hyperbolic_basis (J : HermitianForm 2 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) (z : F) (hz : z * J.conj z = -1) :
    ∃ C : GL (Fin 2) F, J.conjTranspose C.val * J.form * C.val =
      (2 : F) • !![0, 1; 1, 0] := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  let M : Matrix (Fin 2) (Fin 2) F := !![1, 1; z, -z]
  have hdet : M.det ≠ 0 := by
    have he : M.det = -(2 * z) := by simp [M, det_fin_two]; ring
    rw [he]
    exact neg_ne_zero.mpr (mul_ne_zero h2 hz0)
  refine ⟨mkOfDetNeZero M hdet, ?_⟩
  change J.conjTranspose M * J.form * M = _
  rw [hJ, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, HermitianForm.conjTranspose, mul_apply, Fin.sum_univ_two]
  · linear_combination hz
  · linear_combination -hz
  · linear_combination -hz
  · linear_combination hz

private theorem hyperbolic_torus_data (J : HermitianForm 2 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) (z : F) (hz : z * J.conj z = -1) :
    ∃ (ρ : Fˣ →* J.unitarySubgroup) (w : J.unitarySubgroup),
      Function.Injective ρ ∧ w ^ 2 = 1 ∧ w ∉ ρ.range ∧
      (∀ a : Fˣ, w * ρ a * w⁻¹ = ρ ((Units.map J.conj.toMonoidHom a)⁻¹)) ∧
      ∀ a : Fˣ, Units.map J.conj.toMonoidHom a = a⁻¹ →
        (ρ a).val = scalar (Fin 2) a := by
  classical
  obtain ⟨C, hC⟩ := exists_hyperbolic_basis J hJ h2 z hz
  let γ : Fˣ →* Fˣ := Units.map J.conj.toMonoidHom
  have hγ (a : Fˣ) : γ (γ a) = a := by
    apply Units.ext
    exact J.conj_involutive a
  let D : Fˣ →* GL (Fin 2) F :=
    (diagonalPair F).comp ((MonoidHom.id Fˣ).prod (invMonoidHom.comp γ))
  have hD (a : Fˣ) : C * D a * C⁻¹ ∈ J.unitarySubgroup := by
    rw [J.mem_unitarySubgroup_iff, J.conjugate_preserves_iff, hC]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, γ, diagonalPair, HermitianForm.conjTranspose, mul_apply,
        Fin.sum_univ_two]
    · rw [mul_right_comm, mul_inv_cancel₀ ((map_ne_zero J.conj).mpr a.ne_zero), one_mul]
    · rw [J.conj_involutive, mul_right_comm, inv_mul_cancel₀ a.ne_zero, one_mul]
  have hW : C * coordinateSwap F * C⁻¹ ∈ J.unitarySubgroup := by
    rw [J.mem_unitarySubgroup_iff, J.conjugate_preserves_iff, hC]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinateSwap, HermitianForm.conjTranspose, mul_apply, Fin.sum_univ_two]
  let ρ : Fˣ →* J.unitarySubgroup :=
    ((MulAut.conj C).toMonoidHom.comp D).codRestrict J.unitarySubgroup hD
  let w : J.unitarySubgroup := ⟨C * coordinateSwap F * C⁻¹, hW⟩
  have hρinj : Function.Injective ρ := by
    intro a b h
    have hh := (MulAut.conj C).injective (congrArg Subtype.val h)
    exact congrArg Prod.fst (diagonalPair_injective F hh)
  refine ⟨ρ, w, hρinj, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change ((MulAut.conj C) (coordinateSwap F)) ^ 2 = 1
    rw [← map_pow, coordinateSwap_sq, map_one]
  · rintro ⟨a, ha⟩
    have hh := (MulAut.conj C).injective (congrArg Subtype.val ha)
    have he := congrArg (fun A : GL (Fin 2) F => A.val 0 1) hh
    exact zero_ne_one he
  · intro a
    apply Subtype.ext
    change (MulAut.conj C) (coordinateSwap F) * (MulAut.conj C) (D a) *
      ((MulAut.conj C) (coordinateSwap F))⁻¹ = (MulAut.conj C) (D ((γ a)⁻¹))
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg (MulAut.conj C)
    change coordinateSwap F * diagonalPair F (a, (γ a)⁻¹) * (coordinateSwap F)⁻¹ =
      diagonalPair F ((γ a)⁻¹, (γ ((γ a)⁻¹))⁻¹)
    rw [coordinateSwap_conj_diagonalPair, map_inv, hγ, inv_inv]
  · intro a ha
    have he : D a = scalar (Fin 2) a := by
      change diagonalPair F (a, (γ a)⁻¹) = scalar (Fin 2) a
      change γ a = a⁻¹ at ha
      rw [ha, inv_inv]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonalPair, coe_scalar, Matrix.scalar_apply]
    change C * D a * C⁻¹ = scalar (Fin 2) a
    rw [he, ← GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel, mul_one]

/-- The full quadratic-field torus and its inverse-Frobenius reflection,
inside the original standard GU2, with exact norm-one scalar restriction. -/
public theorem exists_unitary_hyperbolic_torus
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0) :
    ∃ (ρ : (GaloisField p (2 * n))ˣ →* GU2 p n hn) (w : GU2 p n hn),
      Function.Injective ρ ∧ w ^ 2 = 1 ∧ w ∉ ρ.range ∧
      (∀ a : (GaloisField p (2 * n))ˣ, w * ρ a * w⁻¹ = ρ ((a ^ (p ^ n))⁻¹)) ∧
      ∀ a : (GaloisField p (2 * n))ˣ, a ^ (p ^ n + 1) = 1 →
        (ρ a).val = scalar (Fin 2) a := by
  obtain ⟨⟨z, _, hz, _, _⟩, _⟩ := unitaryQuadraticCoordinates p n hp hn
  have hp2 : p ≠ 2 := by intro h; obtain ⟨k, hk⟩ := hp; omega
  have h2 : (2 : GaloisField p (2 * n)) ≠ 0 := by
    exact_mod_cast CharP.cast_ne_zero_of_ne_of_prime
      (GaloisField p (2 * n)) Nat.prime_two hp2
  obtain ⟨ρ, w, hi, hw, he, ha, hc⟩ :=
    hyperbolic_torus_data (unitaryForm 2 p n hn) rfl h2 z hz
  have hγ (a : (GaloisField p (2 * n))ˣ) :
      Units.map (unitaryForm 2 p n hn).conj.toMonoidHom a = a ^ (p ^ n) := by
    apply Units.ext
    rfl
  refine ⟨ρ, w, hi, hw, he, ?_, ?_⟩
  · intro a
    rw [ha, hγ]
  · intro a hnorm
    apply hc a
    rw [hγ]
    exact eq_inv_of_mul_eq_one_left (by simpa only [pow_succ] using hnorm)

end ABG

