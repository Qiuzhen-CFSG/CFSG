module

public import Theory.FieldTheory.BinaryTorusInvolution
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Displacement of every nontrivial automorphism of the field of order 64

Every coefficient automorphism is one of the six powers of binary Frobenius.
On the cyclic unit group of order 63, the displacement of its i-th power is
the (2^i-1)-power homomorphism. The five nontrivial possibilities have image
orders 63, 21, 9, 21 and 63, hence every nontrivial field actor has displacement
image of order at least nine. No involution hypothesis is needed.

This is the finite-field calculation used in Aschbacher–Smith, proof of
13.8.20, printed p.954. Identification of a matrix-group actor with a
coefficient automorphism is a separate obligation.
-/

public section

namespace FiniteField.BinarySixDisplacement
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem frobenius_exponent (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6) :
    ∃ i : ℕ, i < 6 ∧ ∀ x : F, σ x = x ^ (2 ^ i) := by
  let : Fintype F := Fintype.ofFinite F
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let σ' : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := σ) (by
    intro x
    have h : σ.toRingHom.comp (algebraMap (ZMod 2) F) = algebraMap (ZMod 2) F :=
      RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x)
  have hd : Module.finrank (ZMod 2) F = 6 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hF, Nat.card_eq_fintype_card, ZMod.card] at hc
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) hc.symm
  obtain ⟨i,hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ZMod 2) F).surjective σ'
  refine ⟨i, hd ▸ i.isLt, ?_⟩
  intro x
  have hx := DFunLike.congr_fun hi x
  change (frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ (i : ℕ)) x = σ x at hx
  simpa only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    pow_iterate, ZMod.card] using hx.symm

theorem card_displacement_ge (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6)
    (hσ : σ ≠ 1) : 9 ≤ Nat.card (BinaryTorusInvolution.displacement σ).range := by
  obtain ⟨i,hi,hpow⟩ := frobenius_exponent σ hF
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hσ
    ext x
    change σ x = x
    simpa only [pow_zero,pow_one] using hpow x
  rw [BinaryTorusInvolution.displacement_eq_power σ hpow,
    IsCyclic.card_powMonoidHom_range, Nat.card_units, hF]
  interval_cases i <;> norm_num at *
end FiniteField.BinarySixDisplacement
