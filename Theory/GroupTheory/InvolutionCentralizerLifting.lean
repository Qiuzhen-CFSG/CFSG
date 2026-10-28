module

public import Theory.GroupTheory.Involution.Basic
public import FeitThompson.BGsection1.CentralizerLemmas

/-!
# Involution centralizers through odd normal subgroups

Coprime centralizer lifting shows that an involution central modulo the odd
core has a centralizer supplementing that core. An element with involutory
image has an involution in its cyclic subgroup with the same image: raise
it to the odd order of its square. Finally, a central involution belongs to
any subgroup covering its coset modulo an odd normal subgroup.

These are the covering and lifting steps used in GLS, Volume 4, Chapter 2,
Lemma 4.7(a). All normality here is in the displayed ambient group, which
can itself be a local subgroup of a larger group.
-/

namespace Theory.GroupTheory
open BenderSuzuki

/-- Odd-core centralizer covering, with the relative group as ambient type. -/
public theorem oddCore_sup_involution_centralizer
    {G : Type*} [Group G] [Finite G] {u : G} (hu : PFAppendixIII.IsInvolution u)
    (hc : QuotientGroup.mk' (pPrimeCore 2 G) u ∈
      Subgroup.center (G ⧸ pPrimeCore 2 G)) :
    pPrimeCore 2 G ⊔ Subgroup.centralizer ({u} : Set G) = ⊤ := by
  let T := Subgroup.zpowers u
  let q := QuotientGroup.mk' (pPrimeCore 2 G)
  have hT : IsPGroup 2 T := by
    apply IsPGroup.of_card (n := 1)
    simp only [T, Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hu.sq_eq_one hu.ne_one
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  have hcentral : T.map q ≤ Subgroup.center (G ⧸ pPrimeCore 2 G) := by
    rw [show T = Subgroup.zpowers u from rfl, q.map_zpowers]
    exact Subgroup.zpowers_le.mpr hc
  have hmap : (Subgroup.centralizer (T : Set G)).map q = ⊤ := by
    rw [← centralizer_map_quotient_eq_map_centralizer 2 T (pPrimeCore 2 G)
      inferInstance (pPrimeCore_coprime_card (p := 2) (G := G))]
    exact Subgroup.centralizer_eq_top_iff_subset.mpr hcentral
  have hcomap := congrArg (Subgroup.comap q) hmap
  simpa only [Subgroup.comap_map_eq, q, QuotientGroup.ker_mk', Subgroup.comap_top,
    T, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, sup_comm] using hcomap

/-- Taking an odd power converts a lift into an involution with the same image. -/
public theorem involution_lift_in_subgroup
    {G : Type*} [Group G] [Finite G] (N A : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) {z : G} (hz : PFAppendixIII.IsInvolution z)
    (hzq : QuotientGroup.mk' N z ≠ 1)
    (himage : QuotientGroup.mk' N z ∈ A.map (QuotientGroup.mk' N)) :
    ∃ w ∈ A, PFAppendixIII.IsInvolution w ∧
      QuotientGroup.mk' N w = QuotientGroup.mk' N z := by
  let q := QuotientGroup.mk' N
  obtain ⟨a, ha, he⟩ := himage
  have ha2 : a ^ 2 ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (a ^ 2) = 1
    rw [map_pow, he, ← map_pow, hz.sq_eq_one, map_one]
  let n : N := ⟨a ^ 2, ha2⟩
  have hk : Odd (orderOf n) := hN.of_dvd_nat (orderOf_dvd_natCard n)
  have heq : q (a ^ orderOf n) = q z := by
    rw [map_pow, he]
    obtain ⟨k, hk⟩ := hk
    rw [hk, pow_add, pow_mul, ← map_pow, hz.sq_eq_one, map_one]
    simp [q]
  refine ⟨a ^ orderOf n, A.pow_mem ha _, ⟨?_, ?_⟩, heq⟩
  · intro hw
    exact hzq (heq.symm.trans (by rw [hw, map_one]))
  · have hn1 := congrArg N.subtype (pow_orderOf_eq_one n)
    change (a ^ 2) ^ orderOf n = 1 at hn1
    simpa only [← pow_mul, Nat.mul_comm] using hn1

/-- Recover the central involution from a subgroup covering its odd-core coset. -/
public theorem involution_mem_of_odd_quotient_image
    {G : Type*} [Group G] [Finite G] (N A : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) {u : G} (hu : PFAppendixIII.IsInvolution u)
    (hc : ∀ a ∈ A, Commute u a)
    (himage : QuotientGroup.mk' N u ∈ A.map (QuotientGroup.mk' N)) : u ∈ A := by
  obtain ⟨a, ha, he⟩ := himage
  have hn : a * u⁻¹ ∈ N := by
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
  let n : N := ⟨a * u⁻¹, hn⟩
  have hodd : Odd (orderOf n) := hN.of_dvd_nat (orderOf_dvd_natCard n)
  have hnu : Commute (n : G) u := by
    dsimp [n]
    exact (hc a ha).symm.mul_left (Commute.refl u).inv_left
  have heq : a = (n : G) * u := by simp [n]
  have hpow : a ^ orderOf n = u := by
    rw [heq, hnu.mul_pow]
    have hn1 : (n : G) ^ orderOf n = 1 := by
      exact congrArg N.subtype (pow_orderOf_eq_one n)
    rw [hn1, one_mul]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_add, pow_mul, hu.sq_eq_one]
    simp
  exact hpow ▸ A.pow_mem ha _

end Theory.GroupTheory
