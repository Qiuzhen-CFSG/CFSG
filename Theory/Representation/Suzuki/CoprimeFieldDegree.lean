module
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.Representation.GeneralLinearNatural
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow

/-!
# Suzuki representations over coprime binary fields

A primitive prime of binary order `4(2m+1)` divides the Suzuki group order.
Over a binary field of odd degree coprime to `2m+1`, its multiplicative order
is unchanged. The general linear group order formula therefore forces every
faithful representation to have field dimension at least `4(2m+1)`.

Disjoint odd prime spectra between Suzuki and SL₃ over a binary field make
the Suzuki degree coprime to three times the linear field degree: a common
divisor would contribute a prime from the Suzuki split factor and the SL₃
cubic order factor. The original
central Hall application supplies this disjointness from its exact action
kernel, then applies the representation obstruction to candidate scalar fields.

Source: Huppert--Blackburn III, XI.3.3 for the Suzuki order; Zsigmondy's
primitive divisor theorem as proved in BinaryPrimitiveDivisor. Application:
Aschbacher--Smith D.3.9 and10.2.3, printed pp.200--201,745.
-/

public noncomputable section
open scoped MatrixGroups
namespace Representation.Suzuki

private theorem relative_prime_degree
    (F : Type*) [Field F] [Finite F] {n p d : ℕ}
    (hF : Nat.card F = 2^n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : p ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) F)) :
    orderOf ((2 : ZMod p)^n) ≤ d := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fact p.Prime := ⟨hp⟩
  rw [Matrix.card_GL_field, ←Nat.card_eq_fintype_card, hF] at hdiv
  obtain ⟨i, _, hi⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff _).mp hdiv
  have hle : (2^n) ^ (i : ℕ) ≤ (2^n) ^ d :=
    Nat.pow_le_pow_right (by positivity) (Nat.le_of_lt i.isLt)
  have hz : ((2 : ZMod p)^n) ^ d - ((2 : ZMod p)^n) ^ (i : ℕ) = 0 := by
    have hh := (ZMod.natCast_eq_zero_iff ((2^n)^d-(2^n)^(i : ℕ)) p).mpr hi
    simpa only [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat] using hh
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have h := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have hpow : ((2 : ZMod p)^n) ^ (d-i) = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero (i : ℕ) (pow_ne_zero n htwo))
    calc
      ((2 : ZMod p)^n) ^ (i : ℕ) * ((2 : ZMod p)^n) ^ (d-i) = ((2 : ZMod p)^n)^d := by
        rw [←pow_add,Nat.add_sub_of_le (Nat.le_of_lt i.isLt)]
      _ = ((2 : ZMod p)^n) ^ (i : ℕ) * 1 := by simpa using sub_eq_zero.mp hz
  exact (orderOf_le_of_pow_eq_one (Nat.sub_pos_of_lt i.isLt) hpow).trans (Nat.sub_le d i)

/-- Over an odd-degree binary field coprime to the Suzuki degree, the full
primitive-prime degree obstruction survives scalar extension. -/
theorem finrank_ge_of_coprime_field_degree
    {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {m n : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2^n) (ho : Odd n) (hc : Nat.Coprime (2*m+1) n)
    (ρ : Representation F (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) V)
    (hf : Function.Injective ρ) : 4*(2*m+1) ≤ Module.finrank F V := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p,hp,hord⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul_odd
    (n := 2*m+1) ⟨m,rfl⟩ (by omega)
  have hp2 : p ≠ 2 := by
    intro hh
    subst p
    rw [show (2 : ZMod 2) = 0 by decide,orderOf_zero] at hord
    omega
  have hd := relative_prime_degree F hF hp hp2
    ((prime_dvd_card_of_orderOf_two (by omega) hp hord).trans
      (Representation.card_dvd_card_GL_of_injective ρ hf))
  have hcn : Nat.Coprime (orderOf (2 : ZMod p)) n := by
    rw [hord]
    have hfour : Nat.Coprime 4 n := by simpa using ho.coprime_two_left.pow_left 2
    exact hfour.mul_left hc
  rwa [hcn.orderOf_pow,hord] at hd

/-- The same bound on a literal matrix embedding. -/
theorem no_small_linear_action_of_coprime_field_degree
    (F : Type*) [Field F] [Finite F] {m n r : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2^n) (ho : Odd n) (hc : Nat.Coprime (2*m+1) n)
    (hr : r < 4*(2*m+1))
    (f : BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m →*
      Matrix.GeneralLinearGroup (Fin r) F) : ¬ Function.Injective f := by
  intro hf
  have h := finrank_ge_of_coprime_field_degree hm hF ho hc
    ((generalLinearNatural r).comp f) ((generalLinearNatural_injective r).comp hf)
  rw [Module.finrank_fin_fun] at h
  omega

/-- Disjoint odd prime spectra for Suzuki and binary SL3 force coprimality
with three times the linear degree; the Suzuki split factor and SL₃ cubic
factor detect every common divisor. -/
theorem field_degree_coprime_of_disjoint_linearThree_primes
    (F : Type*) [Field F] [Finite F] {m n : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2^n)
    (hdis : ∀ p : ℕ, p.Prime → p ≠ 2 →
      p ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
      ¬ p ∣ Nat.card SL(3,F)) : Nat.Coprime (2*m+1) (3*n) := by
  let g := Nat.gcd (2*m+1) (3*n)
  by_contra hc
  have hg : 2 ≤ g := by
    have hp := Nat.gcd_pos_of_pos_left (3*n) (by omega : 0 < 2*m+1)
    change ¬ Nat.gcd (2*m+1) (3*n) = 1 at hc
    omega
  have hpow : 4 ≤ 2^g := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hg
  obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd (by omega : 2^g-1 ≠ 1)
  have hgpos : 0 < 2^g := by positivity
  have hodd : Odd (2^g-1) := Nat.Even.sub_odd hgpos
    (even_two.pow_of_ne_zero (by omega)) odd_one
  have hp2 : p ≠ 2 := by rintro rfl; exact hodd.not_two_dvd_nat hpg
  have hpd : p ∣ 2^(2*m+1)-1 := hpg.trans
    (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.gcd_dvd_left (2*m+1) (3*n)))
  have hpn : p ∣ (2^n)^3-1 := by
    rw [←pow_mul,Nat.mul_comm n 3]
    exact hpg.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.gcd_dvd_right (2*m+1) (3*n)))
  apply hdis p hp hp2
  · rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m hm]
    exact dvd_mul_of_dvd_right hpd _
  · rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpn _) _
end Representation.Suzuki
