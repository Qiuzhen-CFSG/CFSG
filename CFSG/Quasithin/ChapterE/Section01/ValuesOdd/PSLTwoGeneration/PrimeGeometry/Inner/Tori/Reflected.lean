module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Reduction

/-!
# Prime dihedral subgroups of reflected cyclic tori

A reflected cyclic subgroup has twice its cyclic order. If the ambient Sylow
subgroups have order four, the cyclic subgroup has two-part at most two.
An even cyclic subgroup of order greater than two therefore has a nontrivial
odd part. Select a prime divisor, take the cyclic subgroup of twice that prime
order, and adjoin the reflection. Its cyclic involution is central.

This is the torus extraction used in the prime-field branch of
Aschbacher--Smith E.1.14(6), via Aschbacher (1982), Lemma 4.10.
-/

public section

open Subgroup GorensteinWalter

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Tori

variable {G : Type*} [Group G] [Finite G]

private theorem cyclic_subgroup_of_dvd (U : Subgroup G) (hU : IsCyclic U)
    {n : ℕ} (hn : n ∣ Nat.card U) :
    ∃ R : Subgroup G, R ≤ U ∧ IsCyclic R ∧ Nat.card R = n := by
  let : IsCyclic U := hU
  obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top U).mp hU
  have hxU : x ∈ U := by rw [← hx]; exact mem_zpowers x
  have hxo : orderOf x = Nat.card U := by rw [← Nat.card_zpowers, hx]
  let R := zpowers (x ^ (Nat.card U / n))
  have hRU : R ≤ U := zpowers_le.mpr (U.pow_mem hxU _)
  refine ⟨R, hRU, Subgroup.isCyclic_of_le hRU, ?_⟩
  change Nat.card (zpowers (x ^ (Nat.card U / n))) = n
  rw [Nat.card_zpowers, ← hxo]
  exact orderOf_pow_orderOf_div (hxo ▸ Nat.card_pos.ne') (hxo ▸ hn)

private theorem reflected_equiv (R : Subgroup G) (hR : IsCyclic R)
    (w : G) (hwR : w ∉ R) (hw2 : w * w = 1)
    (hwinv : ∀ x : G, x ∈ R → w * x * w⁻¹ = x⁻¹) :
    Nonempty ((R ⊔ zpowers w : Subgroup G) ≃* DihedralGroup (Nat.card R)) := by
  obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top R).mp hR
  have hxR : x ∈ R := by rw [← hx]; exact mem_zpowers x
  let D : Subgroup G := R ⊔ zpowers w
  let ρ : D := ⟨x, (le_sup_left : R ≤ D) hxR⟩
  let σ : D := ⟨w, (le_sup_right : zpowers w ≤ D) (mem_zpowers w)⟩
  have hgen : (⊤ : Subgroup D) = zpowers ρ ⊔ zpowers σ := by
    apply le_antisymm
    · intro y _
      have hy : (y : G) ∈ (zpowers ρ ⊔ zpowers σ).map D.subtype := by
        simp only [Subgroup.map_sup, MonoidHom.map_zpowers]
        change (y : G) ∈ zpowers x ⊔ zpowers w
        rw [hx]
        exact y.property
      obtain ⟨v, hv, heq⟩ := mem_map.mp hy
      exact (Subtype.ext heq : v = y) ▸ hv
    · exact le_top
  have hσ2 : σ ^ 2 = 1 := by
    apply Subtype.ext
    simpa [σ, pow_two] using hw2
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    apply Subtype.ext
    exact hwinv x hxR
  have hσρ : σ ∉ zpowers ρ := by
    intro hm
    apply hwR
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hm
    have heq : x ^ k = w := congrArg Subtype.val hk
    exact heq ▸ R.zpow_mem hxR k
  have hd := dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have horder : orderOf ρ = Nat.card R := by
    rw [← orderOf_injective D.subtype D.subtype_injective, ← Nat.card_zpowers]
    change Nat.card (zpowers x) = Nat.card R
    rw [hx]
  rw [horder] at hd
  exact hd

/-- An even reflected cyclic subgroup larger than two contains a prime dihedral
subgroup with a central involution, if the ambient Sylow two-subgroups have order four. -/
theorem prime_dihedral_of_reflected_cyclic
    (T : Sylow 2 G) (hT : Nat.card T = 4)
    (U : Subgroup G) (hU : IsCyclic U) (heven : 2 ∣ Nat.card U)
    (hlarge : 2 < Nat.card U) (w : G) (hwU : w ∉ U) (hw2 : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹) :
    ∃ (r : ℕ) (D : Subgroup G) (t : G), r.Prime ∧ Odd r ∧
      t ∈ D ∧ IsInvolution t ∧ D ≤ centralizer ({t} : Set G) ∧
      Nonempty (D ≃* DihedralGroup (2 * r)) := by
  obtain ⟨B, _, ⟨eB⟩⟩ := exists_dihedral_two_subgroup_of_cyclic_reflection
    U w hU heven hwU hw2 hwinv
  have hBcard : Nat.card B = 2 ^ ((Nat.card U).factorization 2 + 1) := by
    rw [Nat.card_congr eB.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  obtain ⟨S, hBS⟩ := (IsPGroup.of_card hBcard).exists_le_sylow
  have hBbound : Nat.card B ≤ 4 := by
    calc
      Nat.card B ≤ Nat.card S := Subgroup.card_le_of_le hBS
      _ = Nat.card T := Nat.card_congr (Sylow.equiv S T).toEquiv
      _ = 4 := hT
  have hnotfour : ¬ 4 ∣ Nat.card U := by
    intro hd
    have hv : 2 ≤ (Nat.card U).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hd
    have hp : 2 ^ 3 ≤ 2 ^ ((Nat.card U).factorization 2 + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show Nat.card U / 2 ≠ 1 by
    have := Nat.mod_eq_zero_of_dvd heven
    omega)
  have hrne : r ≠ 2 := by
    intro hr2
    apply hnotfour
    rw [hr2] at hrd
    have hm := Nat.mul_dvd_mul_left 2 hrd
    rwa [Nat.mul_div_cancel' heven] at hm
  have hro : Odd r := hr.odd_of_ne_two hrne
  have h2r : 2 * r ∣ Nat.card U := by
    have hm := Nat.mul_dvd_mul_left 2 hrd
    rwa [Nat.mul_div_cancel' heven] at hm
  obtain ⟨R, hRU, hRc, hRcard⟩ := cyclic_subgroup_of_dvd U hU h2r
  obtain ⟨eD⟩ := reflected_equiv R hRc w (fun hw => hwU (hRU hw)) hw2
    (fun x hx => hwinv x (hRU hx))
  let D : Subgroup G := R ⊔ zpowers w
  let : Fintype R := Fintype.ofFinite R
  let : IsCyclic R := hRc
  let : CommGroup R := IsCyclic.commGroup
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card (G := R) 2 (by
    rw [← Nat.card_eq_fintype_card, hRcard]
    exact dvd_mul_right 2 r)
  have ht2 : t * t = 1 := by
    simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one.mp (show orderOf t ∣ 2 by rw [ht]))
  have htinv : (t : G)⁻¹ = t := by
    apply inv_eq_of_mul_eq_one_left
    exact congrArg Subtype.val ht2
  have hDC : D ≤ centralizer ({(t : G)} : Set G) := by
    apply sup_le
    · intro x hx
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : R) t)
    · apply zpowers_le.mpr
      rw [mem_centralizer_singleton_iff]
      have hi := hwinv t (hRU t.property)
      rw [htinv, mul_inv_eq_iff_eq_mul] at hi
      exact hi
  refine ⟨r, D, t, hr, hro, (le_sup_left : R ≤ D) t.property, ?_, hDC, ?_⟩
  · constructor
    · intro heq
      have : t = 1 := Subtype.ext heq
      simp [this] at ht
    · rw [pow_two]
      exact congrArg Subtype.val ht2
  · rw [hRcard] at eD
    exact ⟨eD⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Tori
