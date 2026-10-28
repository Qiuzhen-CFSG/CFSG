module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerContracts
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Consequences of the literal Sylow-five normalizers

For the source Sylow subgroup P of H = C_G(z), |P| = 5. If |G| = 51840
and |N_G(P)| has two-part four, the Sylow normalizer congruence modulo 25
forces |N_G(P)| = 540. Divisibility leaves just five possible three-parts;
only the three-part 27 satisfies that congruence.

Once V = O₃(N_G(P)) has order 27 and N_H(P) is dihedral of order 20,
z acts fixed-point freely on V. Indeed a fixed element lies in the literal
N_H(P), so its order divides both 27 and 20. The fixed-point-free involution
lemma gives inversion. In particular inversion is proved, rather than a
field of the normalizer-data contract.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.1, printed p.260.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer

variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The Sylow-five subgroup of the distinguished centralizer has order five. -/
theorem ambientFive_card (D : Seed G) (P : Sylow 5 (involutionCentralizer D.z)) :
    Nat.card (ambientFive D P) = 5 := by
  rw [ambientFive, card_map_of_injective (involutionCentralizer D.z).subtype_injective]
  rw [P.card_eq_multiplicity, D.localType.centralizer_card]
  decide +kernel

private theorem arithmetic {n : ℕ} (hn : n ≠ 0) (hd : n ∣ 51840)
    (h5 : 5 ∣ n) (h2 : n.factorization 2 = 2) (hm : n % 25 = 15) : n = 540 := by
  have h4 : 4 ∣ n := by
    have := (Nat.prime_two.pow_dvd_iff_le_factorization hn (k := 2)).mpr (by omega)
    norm_num at this
    exact this
  have h8 : ¬ 8 ∣ n := by
    have := (Nat.prime_two.pow_dvd_iff_le_factorization hn (k := 3))
    norm_num [h2] at this
    exact this
  have h20 : 20 ∣ n :=
    (show Nat.Coprime 4 5 by decide).mul_dvd_of_dvd_of_dvd h4 h5
  obtain ⟨k, hk⟩ := h20
  have hkdiv : k ∣ 2592 := by
    rw [hk] at hd
    have he : 51840 = 20 * 2592 := by decide
    rw [he, Nat.mul_dvd_mul_iff_left (by decide : 0 < 20)] at hd
    exact hd
  have hodd : Odd k := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro he
    obtain ⟨r, hr⟩ := he
    apply h8
    rw [hk, hr]
    exact ⟨5*r, by omega⟩
  have h81 : k ∣ 3 ^ 4 := by
    have he : 2592 = 2^5 * 3^4 := by decide
    rw [he] at hkdiv
    exact (hodd.coprime_two_right.pow_right 5).dvd_of_dvd_mul_left hkdiv
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h81
  interval_cases i <;> norm_num at he <;> subst k <;> norm_num at hk hm ⊢ <;> omega

/-- The Sylow congruence forces normalizer order 540 in the hypothetical
ambient order 51840, once the normalizer has two-part four. -/
theorem fiveNormalizer_card_of_twoPart (D : Seed G)
    (P : Sylow 5 (involutionCentralizer D.z)) (hG : Nat.card G = 51840)
    (h2 : (Nat.card (fiveNormalizer D P)).factorization 2 = 2) :
    Nat.card (fiveNormalizer D P) = 540 := by
  apply arithmetic (Nat.card_pos.ne')
  · simpa only [hG] using (fiveNormalizer D P).card_subgroup_dvd_card
  · rw [← ambientFive_card D P]
    exact card_dvd_of_le le_normalizer
  · exact h2
  · have hc := Sylow.card_normalizer_modEq_card (p := 5) (n := 1)
      (show Nat.card (ambientFive D P) = 5^1 by simpa using ambientFive_card D P)
    change Nat.card (fiveNormalizer D P) % (5^(1+1)) = Nat.card G % (5^(1+1)) at hc
    norm_num [hG] at hc
    exact hc

/-- The three-core has trivial centralizer of z: its fixed elements have
order dividing both 27 and |N_H(P)| = 20. The fixed-point-free involution
therefore acts by inversion. -/
theorem FiveNormalizerData.z_inverts_core {D : Seed G} (N : FiveNormalizerData D) :
    ∀ v ∈ normalizerThreeCore D N.P, D.z * v * D.z⁻¹ = v⁻¹ := by
  let H := involutionCentralizer D.z
  let V := normalizerThreeCore D N.P
  have hPN : ambientFive D N.P ≤ H := map_subtype_le _
  have hzN : D.z ∈ fiveNormalizer D N.P := by
    apply centralizer_le_normalizer (ambientFive D N.P : Set G)
    apply mem_centralizer_iff.mpr
    intro p hp
    exact mem_centralizer_singleton_iff.mp (hPN hp)
  have hzV : D.z ∈ normalizer (V : Set G) := by
    apply (pCore 3 (fiveNormalizer D N.P)).le_normalizer_map (fiveNormalizer D N.P).subtype
    exact mem_map.mpr ⟨⟨D.z, hzN⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  have hVN : V ≤ fiveNormalizer D N.P := pCoreIn_le 3 _
  have hNH : (fiveNormalizer D N.P).comap H.subtype =
      normalizer ((N.P : Subgroup H) : Set H) := by
    rw [fiveNormalizer, comap_normalizer_eq_of_le_range
      (hPN.trans_eq H.range_subtype.symm)]
    rw [ambientFive, comap_map_eq_self_of_injective H.subtype_injective]
  let φ : MulAut V := V.normalizerMonoidHom ⟨D.z, hzV⟩
  have hφ : Function.Involutive φ := by
    have hz2 : D.z ^ 2 = 1 := by
      rw [← D.localType.involution]
      exact pow_orderOf_eq_one D.z
    have he : φ ^ 2 = 1 := by
      change V.normalizerMonoidHom (⟨D.z, hzV⟩ : normalizer (V : Set G)) ^ 2 = 1
      rw [← map_pow, show (⟨D.z, hzV⟩ : normalizer (V : Set G)) ^ 2 = 1 from
        Subtype.ext hz2, map_one]
    exact fun v => congrArg (fun f : MulAut V => f v) he
  have hfree : MonoidHom.FixedPointFree φ := by
    intro v hv
    have hvH : (v : G) ∈ H := by
      have he : D.z * (v : G) * D.z⁻¹ = (v : G) := congrArg Subtype.val hv
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he).symm
    have hvNH : (⟨v, hvH⟩ : H) ∈ normalizer ((N.P : Subgroup H) : Set H) := by
      rw [← hNH]
      exact hVN v.property
    let w : normalizer ((N.P : Subgroup H) : Set H) := ⟨⟨v, hvH⟩, hvNH⟩
    have h27 : orderOf (v : G) ∣ 27 := by
      simpa only [show Nat.card V = 27 from N.core_card] using V.orderOf_dvd_natCard v.property
    have h20 : orderOf (v : G) ∣ 20 := by
      have hh := orderOf_dvd_natCard w
      rw [Nat.card_congr N.localEquiv.toEquiv, DihedralGroup.nat_card] at hh
      change orderOf ((w : H) : G) ∣ 20
      simpa only [orderOf_coe, Nat.reduceMul] using hh
    have hd := Nat.dvd_gcd h27 h20
    norm_num at hd
    exact hd
  intro v hv
  exact congrArg Subtype.val (congrFun (hfree.coe_eq_inv_of_involutive hφ) ⟨v, hv⟩)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
