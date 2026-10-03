module
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow

/-!
# Normal subgroups avoiding a central involution

If every Sylow two-subgroup has center of order two, a normal subgroup
avoiding a specified central involution has odd order and lies in the odd
core. Otherwise a nontrivial normal intersection with a Sylow subgroup meets
its center, forcing the specified involution into the normal subgroup.

This isolates the kernel argument in ABG III.8 Lemma 2, article p.115.
-/

namespace Subgroup

/-- A normal subgroup avoiding a central involution has odd order if the
centers of the Sylow two-subgroups have order two. -/
public theorem odd_card_of_not_mem_central_involution
    {H : Type*} [Group H] [Finite H]
    (hcenter : ∀ P : Sylow 2 H, Nat.card (center P) = 2)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ center H)
    (K : Subgroup H) [K.Normal] (hzK : z ∉ K) : Odd (Nat.card K) := by
  classical
  by_contra hodd
  have heven : 2 ∣ Nat.card K := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 heven
  have haH : orderOf (a : H) = 2 := (orderOf_coe a).trans ha
  have hp : IsPGroup 2 (zpowers (a : H)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, haH, pow_one]
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have haP : (a : H) ∈ P := hP (mem_zpowers _)
  let L : Subgroup P := K.subgroupOf P
  let aP : P := ⟨a, haP⟩
  have haL : aP ∈ L := a.property
  have haPne : aP ≠ 1 := by
    intro h
    have he : (a : H) = 1 := congrArg Subtype.val h
    simp [he] at haH
  let : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr (by
    intro hL
    have := hL ▸ haL
    exact haPne (mem_bot.mp this))
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  obtain ⟨v, hv, hvc⟩ := exists_nontrivial_center_mem_normal (p := 2) L
  have hzcentral : zpowers z ≤ center H := zpowers_le.mpr hzc
  let : (zpowers z).Normal := ⟨by
    intro g hg k
    have hc := mem_center_iff.mp (hzcentral hg) k
    simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using hg⟩
  have hzpow : IsPGroup 2 (zpowers z) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hz, pow_one]
  have hzP : z ∈ P := hzpow.le_sylow_of_normal P (mem_zpowers _)
  let zP : P := ⟨z, hzP⟩
  have hzPc : zP ∈ center P := by
    apply mem_center_iff.mpr
    intro g
    exact Subtype.ext (mem_center_iff.mp hzc g)
  have hzPne : zP ≠ 1 := by
    intro h
    have he : z = 1 := congrArg Subtype.val h
    simp [he] at hz
  obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp (hcenter P)
  have heq : (v : P) = zP := by
    have he : (⟨v, hvc⟩ : center P) = ⟨zP, hzPc⟩ := (hw (⟨v, hvc⟩ : center P) (by
      intro h
      exact hv (Subtype.ext (congrArg (fun y : center P => (y : P)) h)))).trans
      (hw (⟨zP, hzPc⟩ : center P) (by
        intro h
        exact hzPne (congrArg (fun y : center P => (y : P)) h))).symm
    exact congrArg (fun y : center P => (y : P)) he
  have hzPL : zP ∈ L := by rw [← heq]; exact v.property
  exact hzK hzPL

/-- Every normal subgroup avoiding the distinguished central involution
lies in the odd core. -/
public theorem le_oddCore_of_not_mem_central_involution
    {H : Type*} [Group H] [Finite H]
    (hcenter : ∀ P : Sylow 2 H, Nat.card (center P) = 2)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ center H)
    (K : Subgroup H) [K.Normal] (hzK : z ∉ K) : K ≤ pPrimeCore 2 H := by
  exact le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr
    (odd_card_of_not_mem_central_involution hcenter z hz hzc K hzK)⟩

end Subgroup
