module

public import Theory.PGroupCore
import Mathlib.Tactic.Linarith

/-!
# Odd indices and intrinsic two-core orders

If |G| = q · 2ᵃ · m with m odd, an odd-index subgroup H with
|H/O₂(H)| = q has index m and two-core order 2ᵃ. Lagrange gives
2ⁿ[ G : H ] = 2ᵃm; coprimality identifies the two odd factors.

This supplies the order reduction in Aschbacher–Smith, *The Classification
of Quasithin Groups*, B.4.12(2), printed p.97 of `refs/quasithin.pdf`.
-/

public section

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem index_and_card_twoCore_of_odd (H : Subgroup G) {q a m : ℕ}
    (hG : Nat.card G = q * 2 ^ a * m) (hq : 0 < q) (hm : Odd m)
    (hindex : Odd H.index) (hquot : Nat.card (H ⧸ pCore 2 H) = q) :
    H.index = m ∧ Nat.card (pCore 2 H) = 2 ^ a := by
  have hH : Nat.card (pCore 2 H) * q = Nat.card H := by
    simpa only [Subgroup.index, hquot] using (pCore 2 H).card_mul_index
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have he : 2 ^ n * H.index = 2 ^ a * m := by
    have ht := H.card_mul_index
    rw [← hH, hn, hG] at ht
    nlinarith
  have hic : Nat.Coprime H.index (2 ^ a) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hindex.not_two_dvd_nat).symm.pow_right a
  have hmc : Nat.Coprime m (2 ^ n) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hm.not_two_dvd_nat).symm.pow_right n
  have hi : H.index = m := Nat.dvd_antisymm
    (hic.dvd_of_dvd_mul_left (he ▸ dvd_mul_left H.index (2 ^ n)))
    (hmc.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left m (2 ^ a)))
  refine ⟨hi, ?_⟩
  rw [hi] at he
  rw [hn]
  have hi0 : 0 < H.index := Nat.card_pos
  have hm0 : 0 < m := hi ▸ hi0
  nlinarith
end Subgroup
