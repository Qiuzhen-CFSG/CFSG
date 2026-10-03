module

public import Theory.Character.ModularBlock.MixedBrauerTrace
public import Theory.Representation.IntegralSpectralTrace
public import Theory.GroupTheory.PrimeRegularDecomposition
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Integral mixed traces at prime-singular and prime-regular elements

Let `R` be a local domain in which the prime `p` is not a unit and which
contains primitive roots for all divisors of the finite group order. For a
central idempotent `e` of `R[G]`, the projected left-right trace at `u,v`
vanishes whenever `p` divides the order of `u` but not the order of `v`.

Decompose `u = t * a` into commuting prime-power and prime-regular parts.
Translation by the nonidentity element `t` has no fixed group-basis vectors.
The left-right permutation for `a,v` has exponent the least common multiple
of their orders, which divides the group order and is a unit in `R`.
Integral spectral projectors then reduce the trace to the fixed-point-free
prime-power permutation trace theorem. Only commutation of `t` with `a`
is needed; the prime part need not be central in the group.

Source: the integral permutation-summand argument documented in
`Theory.Representation.IntegralSpectralTrace`, applied to the mixed trace in
Brauer--Tuan (1945), equation (2.3).
-/

public section

noncomputable section
attribute [local instance] Fintype.ofFinite
namespace ModularBlock.PrimeRegularTrace
open BrauerConjugationTrace MixedBrauerTrace MixedConjugationTrace

/-- A central idempotent has zero integral mixed trace between a prime-singular
and a prime-regular element. No characteristic-zero assumption is needed. -/
theorem trace_projectedLeftRight_eq_zero
    {R G : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (hp : ¬ IsUnit (p : R))
    (hroots : ∀ n : ℕ, n ∣ Nat.card G → ∃ ζ : R, IsPrimitiveRoot ζ n)
    (e : MonoidAlgebra R G) (he : IsIdempotentElem e)
    (hec : e ∈ Set.center (MonoidAlgebra R G))
    (u v : G) (hu : p ∣ orderOf u) (hv : ¬ p ∣ orderOf v) :
    LinearMap.trace R (MonoidAlgebra R G) (projectedLeftRight e u v) = 0 := by
  classical
  let : CharP (IsLocalRing.ResidueField R) p := by
    apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    rw [← map_natCast (IsLocalRing.residue R)]
    exact not_ne_iff.mp (fun h => hp ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h))
  obtain ⟨t, a, ⟨k, htk⟩, ha, hcomm, hta⟩ :=
    exists_commuting_prime_parts p Fact.out u
  have ht : t ≠ 1 := by
    intro ht
    apply ha
    rw [ht, one_mul] at hta
    exact hta.symm ▸ hu
  let σ := leftRightPerm t 1
  let τ := leftRightPerm a v
  let U := τ.permMatrix R
  let P := rightMatrix e
  let n := Nat.lcm (orderOf a) (orderOf v)
  have hn : n ≠ 0 := (Nat.lcm_pos (orderOf_pos a) (orderOf_pos v)).ne'
  have hpn : ¬ p ∣ n := by
    intro hd
    exact (Fact.out : p.Prime).not_dvd_mul ha hv (hd.trans (Nat.lcm_dvd_mul _ _))
  have hnunit : IsUnit (n : R) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_natCast]
    exact fun hz => hpn ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) p n).mp hz)
  obtain ⟨ζ, hζ⟩ := hroots n (leftRight_lcm_dvd_card a v)
  have hσ : σ ^ (p ^ k) = 1 := leftRightPerm_pow_eq_one t 1 htk (one_pow _)
  have hfix : ∀ x, σ x ≠ x := by
    intro x hx
    exact ht (inv_eq_one.mp (mul_right_cancel (b := x) (by simpa [σ] using hx)))
  have hU : U ^ n = 1 := by
    rw [← Matrix.permMatrix_pow]
    rw [show τ ^ n = 1 from leftRightPerm_lcm_pow_eq_one a v]
    exact Matrix.permMatrix_one
  have hTU : Commute (σ.permMatrix R) U := by
    change σ.permMatrix R * τ.permMatrix R = τ.permMatrix R * σ.permMatrix R
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
    congr 1
    ext x
    simp only [σ, τ, Equiv.Perm.mul_apply, leftRightPerm_apply, mul_one]
    simp only [← mul_assoc]
    rw [hcomm.inv_inv.eq]
  have hz := Matrix.trace_permMatrix_mul_mul_eq_zero_of_prime
    (IsLocalRing.residue R) IsLocalRing.residue_surjective
    (fun r hr => (IsLocalRing.residue_ne_zero_iff_isUnit r).mp hr)
    σ hσ hfix U P (rightMatrix_isIdempotent e he)
    (rightMatrix_commute_leftRight e hec t 1)
    (rightMatrix_commute_leftRight e hec a v) hTU hn hU hnunit ζ hζ
  have hfactor : σ.permMatrix R * U = (leftRightPerm u v).permMatrix R := by
    rw [← Matrix.permMatrix_mul]
    congr 1
    ext x
    simp only [σ, τ, Equiv.Perm.mul_apply, leftRightPerm_apply, mul_one,
      ← hta, mul_inv_rev, mul_assoc]
  rw [hfactor] at hz
  exact (trace_permMatrix_mul_rightMatrix e u v).symm.trans hz

end ModularBlock.PrimeRegularTrace
