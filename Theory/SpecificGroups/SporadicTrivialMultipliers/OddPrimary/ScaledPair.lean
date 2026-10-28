module
public import Theory.GroupTheory.PerfectCentralCoverSimultaneousInversion
import all Theory.GroupTheory.PerfectCentralCoverSimultaneousInversion
import all Theory.GroupTheory.PerfectCentralCoverSylowNine

/-!
# Power actions in perfect central covers

If an actor fixes one member of a commuting pair and raises the other to
its k-th power, the commutator of any lifts is killed by k−1. The order of
the first member kills it as well. Coprimality therefore makes the lifts
commute. Applied twice to a nonabelian Sylow pair and its central commutator,
this gives the same central Sylow transfer as simultaneous inversion.
The actual Held seven-subgroup below uses k=2 and k=4.

The intentional private imports reuse the internal lift-generation and
pair-commutator lemmas from the existing transfer proof, preserving its
public boundary and avoiding changes in shared foundational modules.
Source: Aschbacher–Smith I.1.3, printed p.407; GLS III Table 5.3p.
-/

open Subgroup
open scoped commutatorElement
namespace SporadicTrivialMultipliers.OddPrimary
open PerfectCentralCovering

private theorem commute_lifts_of_power_fixed
    {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (x y r : G) {n k : ℕ} (hn : n.Coprime (k - 1)) (hk1 : 1 ≤ k)
    (hx : x ^ n = 1) (hxy : Commute x y)
    (hrx : r * x * r⁻¹ = x ^ k) (hry : Commute r y)
    (a b : E) (ha : f a = x) (hb : f b = y) : Commute a b := by
  have hc : ⁅a,b⁆ ∈ center E := hk (by
    rw [MonoidHom.mem_ker, map_commutatorElement, ha, hb]
    exact hxy.commutator_eq)
  have hconj (t : E) : t * ⁅a,b⁆ * t⁻¹ = ⁅a,b⁆ := by
    rw [mem_center_iff.mp hc t, mul_inv_cancel_right]
  have hpow (l : ℕ) : ⁅a ^ l,b⁆ = ⁅a,b⁆ ^ l := by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [pow_succ, commutatorElement_mul_left_eq_conj_mul, hconj, ih, pow_succ']
  obtain ⟨s, hs⟩ := hf r
  have he : ⁅a,b⁆ = ⁅a,b⁆ ^ k := by
    rw [← hpow k, ← hconj s, conjugate_commutatorElement]
    apply CentralExtension.commutator_eq_of_image_eq f hk
    · simp only [map_mul, map_inv, map_pow, hs, ha, hrx]
    · simp only [map_mul, map_inv, hs, hb]
      rw [hry.eq, mul_inv_cancel_right]
  have hkm : ⁅a,b⁆ ^ (k - 1) = 1 := by
    rw [pow_sub _ hk1, pow_one, ← he, mul_inv_cancel]
  have hncomm : ⁅a,b⁆ ^ n = 1 := by
    rw [← hpow]
    apply Commute.commutator_eq
    exact (mem_center_iff.mp (hk (by
      rw [MonoidHom.mem_ker, map_pow, ha, hx])) b).symm
  apply commutatorElement_eq_one_iff_mul_comm.mp
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hn
    (orderOf_dvd_of_pow_eq_one hncomm) (orderOf_dvd_of_pow_eq_one hkm))

public theorem not_dvd_card_kernel_of_scaled_pair
    {E G : Type*} [Group E] [Finite E] [Group.IsPerfect E] [Group G] [Finite G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    {p : ℕ} [Fact p.Prime] (i j : ℕ) (hi : p.Coprime (i - 1)) (hj : p.Coprime (j - 1))
    (hi1 : 1 ≤ i) (hj1 : 1 ≤ j) (Q : Sylow p G) (x y r : G)
    (hQ : closure ({x, y} : Set G) = (Q : Subgroup G))
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hxz : Commute x ⁅x, y⁆) (hyz : Commute y ⁅x, y⁆)
    (hrx : r * x * r⁻¹ = x ^ i) (hry : r * y * r⁻¹ = y ^ j)
    (hrz : Commute r ⁅x, y⁆) : ¬ p ∣ Nat.card f.ker := by
  obtain ⟨P, hPQ⟩ := Sylow.mapSurjective_surjective hf p Q
  have hmap : (P : Subgroup E).map f = (Q : Subgroup G) := by
    rw [← Sylow.coe_mapSurjective hf, hPQ]
  have hxmem : x ∈ (P : Subgroup E).map f := by
    rw [hmap, ← hQ]
    exact subset_closure (by simp)
  have hymem : y ∈ (P : Subgroup E).map f := by
    rw [hmap, ← hQ]
    exact subset_closure (by simp)
  obtain ⟨aE, haP, ha⟩ := hxmem
  obtain ⟨bE, hbP, hb⟩ := hymem
  let a : P := ⟨aE, haP⟩
  let b : P := ⟨bE, hbP⟩
  let c : P := ⁅a, b⁆
  have hfc : f (c : E) = ⁅x, y⁆ := by
    change f ⁅aE, bE⁆ = _
    rw [map_commutatorElement, ha, hb]
  have hgen : closure ({a, b} : Set P) = ⊤ :=
    pair_lifts_generate f hk P a b (by
      change closure ({f aE, f bE} : Set G) = _
      rw [ha, hb, hQ, hmap])
  have hca : Commute c a := by
    apply Subtype.ext
    exact (commute_lifts_of_power_fixed f hf hk
      x ⁅x, y⁆ r hi hi1 hx hxz hrx hrz aE c ha hfc).symm.eq
  have hcb : Commute c b := by
    apply Subtype.ext
    exact (commute_lifts_of_power_fixed f hf hk
      y ⁅x, y⁆ r hj hj1 hy hyz hry hrz bE c hb hfc).symm.eq
  have hder : _root_.commutator P ≤ zpowers c :=
    SylowNine.commutator_le_zpowers_of_pair a b hgen hca hcb
  have hcp : c ^ p = 1 := by
    apply pow_commutator a b hca
    apply Subtype.ext
    exact (mem_center_iff.mp (hk (by
      change f (aE ^ p) = 1
      rw [map_pow, ha, hx])) bE).symm
  have hcorder : orderOf c = p := orderOf_eq_prime hcp (by
    intro hc
    apply hz
    rw [← hfc, hc, Subgroup.coe_one, map_one])
  have hzorder : orderOf ⁅x, y⁆ = p := orderOf_eq_prime (by
    rw [← hfc, ← map_pow]
    exact (congrArg f (congrArg Subtype.val hcp)).trans (map_one f)) hz
  intro hd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hd
  have hwE : orderOf (w : E) = p := (Subgroup.orderOf_coe w).trans hw
  let W := zpowers (w : E)
  have hW : W ≤ center E := zpowers_le.mpr (hk w.property)
  let : W.Normal := ⟨fun v hv g => by
    rw [mem_center_iff.mp (hW hv) g, mul_inv_cancel_right]
    exact hv⟩
  have hWp : IsPGroup p W := IsPGroup.of_card (n := 1) (by
    simpa only [W, Nat.card_zpowers, pow_one] using hwE)
  have hwP : (w : E) ∈ (P : Subgroup E) := hWp.le_sylow_of_normal P (mem_zpowers _)
  have hwder := center_inf_commutator_inf_sylow_le_commutator P
    ⟨⟨hk w.property, Group.IsPerfect.mem_commutator⟩, hwP⟩
  rw [← map_subtype_commutator] at hwder
  obtain ⟨v, hv, hvw⟩ := hwder
  obtain ⟨k, hkpow⟩ := mem_zpowers_iff.mp (hder hv)
  have hpowimage : ⁅x, y⁆ ^ k = 1 := by
    rw [← hfc, ← map_zpow]
    exact (congrArg f ((congrArg Subtype.val hkpow).trans hvw)).trans w.property
  have hcpow : c ^ k = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by
    rw [hcorder, ← hzorder]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hpowimage)
  have hwone : (w : E) = 1 := by
    rw [← hvw, ← hkpow, hcpow, map_one]
  rw [hwone, orderOf_one] at hwE
  exact (Fact.out : p.Prime).ne_one hwE.symm

end SporadicTrivialMultipliers.OddPrimary
