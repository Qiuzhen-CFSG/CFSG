module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.CardBounds
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Excluding binary PSU₃ from odd-prime PSL₂

For q = 2^f ≥ 4, the actual PSU₃(q) matrix group contains a subgroup of
order q³ and has order (q³+1)q³(q²−1)/gcd(3,q+1). Its order is too small
to be an odd PSL₂(p), since the latter's two-part forces p ≥ q³−1.

The unitary witness may have any nondegenerate Hermitian Gram matrix.
The imported field calculation derives the fixed-field order from the
prescribed Frobenius map, and Huppert II.10.4 supplies a basis change.
Conjugation in PGL transports the actual projective groups before applying
the root-subgroup and order calculations of Huppert II.10.12.

This is the unitary comparison for Aschbacher–Smith, full 1.1.5(3),
printed pp.501–503, used in the proof of 15.4.20, printed p.1164.
The full characteristic-two list is assembled separately in LieParameter.
-/

open Matrix BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter

variable {Q : Type*} [Group Q]

private theorem unitary_card_bounds {f : ℕ} (hf : 2 ≤ f)
    (h : ClassicalGroup.IsPSU Q 3 (2^f)) :
    2^(f*3) ∣ Nat.card Q ∧
      Nat.card Q ≤ ((2^f)^3+1)*(2^f)^3*((2^f)^2-1) := by
  rcases h with ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J f (by omega) hcard hconj
  let K := FormTransport.standardForm J
  let e' := e.trans (FormTransport.projectiveEquiv J C hC)
  have hfixed : Nat.card {x : F // K.conj x = x} = 2^f :=
    fixed_card J f (by omega) hcard hconj
  rcases BenderSuzuki.External.huppert_II_10_12 K (2^f) hcard hfixed rfl with
    ⟨_, _rho, _pinf, _hrho, _hnatural, _hUcard, hroot, _htwo, horder, _hthree⟩
  have he : Nat.card Q = Nat.card (ProjectiveSpecialUnitaryMatrixGroup K) :=
    Nat.card_congr e'.toEquiv
  constructor
  · rcases hroot with ⟨R, H, _, _, _, _, _, _, hRcard, _⟩
    rw [he, pow_mul, ← hRcard]
    exact R.card_subgroup_dvd_card
  · rw [he, horder]
    exact Nat.div_le_self _ _

private theorem unitary_order_estimate {q : ℕ} (hq : 4 ≤ q) :
    (q^3+1)*q^3*(q^2-1) ≤ q^3*(q^3-1)*(q^2+1) ∧
      2*(q^2+1)+2 < q^3 := by
  have hsq : 1 ≤ q^2 := by nlinarith
  have hcube : q^2 ≤ q^3 := by nlinarith [sq_nonneg q]
  have hs2 : q^2-1+1=q^2 := Nat.sub_add_cancel hsq
  have hs3 : q^3-1+1=q^3 := Nat.sub_add_cancel (by omega)
  constructor
  · have h : (q^3+1)*(q^2-1) ≤ (q^3-1)*(q^2+1) := by nlinarith
    calc
      _ = q^3*((q^3+1)*(q^2-1)) := by ring
      _ ≤ q^3*((q^3-1)*(q^2+1)) := Nat.mul_le_mul_left _ h
      _ = _ := by ring
  · nlinarith [sq_nonneg (q-4)]

/-- An odd-prime PSL₂ is never PSU₃(2^f) for f ≥ 2, for any of the
nondegenerate Hermitian forms allowed by the classical-model interface. -/
public theorem not_unitary {p f : ℕ} (_hp : p.Prime) (ho : Odd p) (hp5 : 5 ≤ p)
    (hodd : ClassicalGroup.IsPSL Q 2 p) (hf : 2 ≤ f)
    (hunitary : ClassicalGroup.IsPSU Q 3 (2^f)) : False := by
  obtain ⟨hd, hc⟩ := unitary_card_bounds hf hunitary
  have hq : 4 ≤ 2^f := by
    exact Nat.pow_le_pow_right (by omega : 0 < 2) hf
  obtain ⟨hbound, hsmall⟩ := unitary_order_estimate hq
  apply not_of_two_power_order_product ho (by omega) hodd hd
    (b := (2^f)^2+1)
  · simpa only [pow_mul] using hc.trans hbound
  · simpa only [pow_mul] using hsmall

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter
