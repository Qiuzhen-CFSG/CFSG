module

public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow

/-!
# Independent inversion in a two-generator torus

A central commutator of lifts is fixed by every inner automorphism upstairs.
An ambient element inverting the first generator and fixing the second
also inverts that commutator. Its order divides both two and the odd order
of the first generator, so it is trivial. The two lifted generators and
the central kernel therefore generate an abelian full preimage.

The Sylow specialization excludes an odd prime from a perfect central
kernel. The geometric input describes actual generators and conjugation,
with no assumption about the cover or its multiplier.

Source: the torus-transfer proof of the nondefining part of Sp₄(2ⁿ)'s
multiplier calculation, Aschbacher–Smith I.1.2–I.1.3, printed p.407,
citing GLS98 §6.1.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace PerfectCentralCovering

/-- Two commuting generators, with one independently inverted by conjugation. -/
public structure InvertedGenerators {G : Type*} [Group G] (H : Subgroup G) where
  left : H
  right : H
  commute : Commute (left : G) (right : G)
  normalForm : ∀ z : H, ∃ i j : ℤ, (z : G) = (left : G)^i * (right : G)^j
  inverter : G
  invert_left : inverter * (left : G) * inverter⁻¹ = (left : G)⁻¹
  fix_right : inverter * (right : G) * inverter⁻¹ = (right : G)

private theorem commute_lifts_of_odd_inversion
    {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hk : f.ker ≤ center E) (a b w : E)
    (hab : Commute (f a) (f b)) (ha : f (w*a*w⁻¹) = f a⁻¹)
    (hb : f (w*b*w⁻¹) = f b) (hodd : Odd (orderOf (f a))) :
    Commute a b := by
  have hc : ⁅a,b⁆ ∈ center E := hk (by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact hab.commutator_eq)
  have hinv : ⁅a,b⁆ = ⁅a,b⁆⁻¹ := by
    calc
      ⁅a,b⁆ = w * ⁅a,b⁆ * w⁻¹ := by
        rw [mem_center_iff.mp hc w]
        simp [mul_assoc]
      _ = ⁅w*a*w⁻¹,w*b*w⁻¹⁆ := conjugate_commutatorElement _ _ _
      _ = ⁅a⁻¹,b⁆ := CentralExtension.commutator_eq_of_image_eq f hk ha hb
      _ = ⁅a,b⁆⁻¹ := by
        rw [commutatorElement_inv_left, ← commutatorElement_inv,
          mem_center_iff.mp ((center E).inv_mem hc) a⁻¹]
        simp [mul_assoc]
  have hsq : ⁅a,b⁆^2 = 1 := by
    rw [pow_two]
    conv_lhs => lhs; rw [hinv]
    exact inv_mul_cancel _
  have hpows (n : ℕ) : ⁅a^n,b⁆ = ⁅a,b⁆^n := by
    have hca : Commute ⁅a,b⁆ a := (mem_center_iff.mp hc a).symm
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, commutatorElement_mul_left_eq_conj_mul,
        hca.symm.pow_left n |>.eq, mul_inv_cancel_right, ih, ← pow_succ']
  have hpow : ⁅a,b⁆ ^ orderOf (f a) = 1 := by
    rw [← hpows]
    exact (show Commute (a ^ orderOf (f a)) b from
      (mem_center_iff.mp (hk (by simp only [MonoidHom.mem_ker, map_pow,
        pow_orderOf_eq_one])) b).symm).commutator_eq
  apply commutatorElement_eq_one_iff_commute.mp
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right
    (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one hsq)

/-- Odd order kills the central commutator detected by independent inversion. -/
public theorem InvertedGenerators.abelian_preimage
    {E G : Type*} [Group E] [Group G] (H : Subgroup G)
    (h : InvertedGenerators H) (hodd : Odd (Nat.card H))
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    IsMulCommutative (H.comap f) := by
  obtain ⟨a, ha⟩ := hf h.left
  obtain ⟨b, hb⟩ := hf h.right
  obtain ⟨w, hw⟩ := hf h.inverter
  have hcomm : Commute a b := commute_lifts_of_odd_inversion f hk a b w
    (by simpa only [ha, hb] using h.commute)
    (by simpa only [map_mul, map_inv, hw, ha] using h.invert_left)
    (by simpa only [map_mul, map_inv, hw, hb] using h.fix_right)
    (by simpa only [ha, Subgroup.orderOf_coe] using
      hodd.of_dvd_nat (orderOf_dvd_natCard h.left))
  have hform (z : E) (hz : z ∈ H.comap f) :
      ∃ (k : E) (i j : ℤ), k ∈ center E ∧ z = k * (a^i * b^j) := by
    obtain ⟨i, j, hij⟩ := h.normalForm ⟨f z, hz⟩
    change f z = (h.left : G)^i * (h.right : G)^j at hij
    let k := z * (a^i * b^j)⁻¹
    refine ⟨k, i, j, hk ?_, ?_⟩
    · change f (z * (a^i * b^j)⁻¹) = 1
      simp only [map_mul, map_inv, map_zpow, ha, hb, hij, mul_inv_cancel]
    · simp only [k, inv_mul_cancel_right]
  have hcent (k : E) (hk : k ∈ center E) (z : E) : Commute k z :=
    (mem_center_iff.mp hk z).symm
  apply IsMulCommutative.of_setLike_mul_comm
  intro z hz v hv
  obtain ⟨k, i, j, hk, hz⟩ := hform z hz
  obtain ⟨l, m, n, hl, hv⟩ := hform v hv
  rw [hz, hv]
  apply Commute.eq
  apply (hcent k hk _).mul_left
  apply (hcent l hl _).symm.mul_right
  exact ((Commute.zpow_zpow_self ..).mul_right (hcomm.zpow_zpow i n)).mul_left
    ((hcomm.symm.zpow_zpow j m).mul_right (Commute.zpow_zpow_self ..))

/-- Apply the inversion criterion to the literal Sylow preimage and transfer. -/
public theorem not_dvd_card_kernel_of_inverted_sylow
    {E G : Type*} [Group E] [Finite E] [Group.IsPerfect E] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (Q : Sylow p G)
    (hQ : InvertedGenerators (Q : Subgroup G))
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ p ∣ Nat.card f.ker := by
  apply not_dvd_card_kernel_of_abelian_sylow_preimage f hf hk Q
  apply hQ.abelian_preimage _ ?_ f hf hk
  obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
  rw [hn]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow

end PerfectCentralCovering
