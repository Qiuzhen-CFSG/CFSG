module

public import Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
import all Theory.SpecificGroups.SymmetricFive.OuterFourGeometry

/-!
# Cubic displacement of an outer four-group in S₅

An elementary two-subgroup of a Sylow two-subgroup of S₅ has order at most four.
For an outer four-group B, a cubic normalizing the Sylow's even four-group has
B ∩ Bᵈ = 1. Sylow conjugacy transports the marked eight- and four-word models.
The finite certificate checks individual five-point permutations and their
conjugation of one marked even involution, rather than a subgroup lattice.

This supplies the permutation-image intersection in Aschbacher–Smith,
proof of 6.2.13, p.688; the source lift identifies the intersection with ZS.
-/

public section
open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricFive.OuterFourIntersection
open OuterFourGeometry

private theorem certificate : ∀ d : D, d ^ 3 = 1 → d ≠ 1 →
    (∃ k, word k = d * (a * b) * d⁻¹) →
    ∀ i j, fourWord i = d⁻¹ * fourWord j * d → fourWord i = 1 := by
  decide +kernel

private theorem positioned_test (d : D) (hd : orderOf d = 3)
    (hn : d ∈ normalizer ((eight ⊓ alternatingGroup (Fin 5) : Subgroup D) : Set D)) :
    four ⊓ four.map (MulAut.conj d⁻¹).toMonoidHom = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro x ⟨⟨i, hi⟩, y, ⟨j, hj⟩, hxy⟩
  have he : a * b ∈ eight ⊓ alternatingGroup (Fin 5) := by
    refine ⟨⟨3, rfl⟩, ?_⟩
    exact Perm.mem_alternatingGroup.mpr (by decide +kernel)
  have hm := (mem_normalizer_iff.mp hn (a * b)).mp he
  have hp : d ^ 3 = 1 := hd ▸ pow_orderOf_eq_one d
  have hne : d ≠ 1 := by intro h; simp [h] at hd
  have hc := certificate d hp hne hm.1 i j
  apply mem_bot.mpr
  rw [← hi]
  apply hc
  change d⁻¹ * y * (d⁻¹)⁻¹ = x at hxy
  simpa only [inv_inv, hi, hj] using hxy.symm

private theorem positioned_card_le_four (B : Subgroup D) [IsElementaryAbelian 2 B] (hB : B ≤ eight) :
    Nat.card B ≤ 4 := by
  have hd : Nat.card B ∣ 2 ^ 3 := by
    simpa only [eight_card, show (2 : ℕ) ^ 3 = 8 from rfl] using card_dvd_of_le hB
  obtain ⟨k, hk, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hn : Nat.card B ≠ 8 := by
    intro h
    have he : B = eight := eq_of_le_of_card_ge hB (by rw [h, eight_card])
    have hx : a * c ∈ B := he ▸ (show a * c ∈ eight from ⟨5, rfl⟩)
    have hp : (a * c) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (a * c) hx
    have hnp : (a * c) ^ 2 ≠ 1 := by decide +kernel
    exact hnp hp
  have hk2 : k ≤ 2 := by
    by_contra h
    have hk3 : k = 3 := by omega
    subst k
    exact hn hc
  rw [hc]
  interval_cases k <;> norm_num

/-- A cubic normalizing the even part of the prescribed Sylow moves an outer
four-group to a four-group with trivial intersection. -/
theorem outer_four_inf_cubic_conjugate (T : Sylow 2 D) (B : Subgroup D)
    [IsElementaryAbelian 2 B]
    (hcard : Nat.card B = 4) (hBT : B ≤ (T : Subgroup D))
    (hout : ¬ B ≤ alternatingGroup (Fin 5)) (d : D)
    (hd : orderOf d = 3)
    (hn : d ∈ normalizer (((T : Subgroup D) ⊓ alternatingGroup (Fin 5) : Subgroup D) : Set D)) :
    B ⊓ B.map (MulAut.conj d⁻¹).toMonoidHom = ⊥ := by
  obtain ⟨e, hT, hB⟩ := exists_marking T B hcard hBT hout
  have hA : (alternatingGroup (Fin 5)).map e.toMonoidHom = alternatingGroup (Fin 5) :=
    characteristic_iff_map_eq.mp inferInstance e
  have hn' := mem_map_of_mem e.toMonoidHom hn
  rw [map_equiv_normalizer_eq, map_inf _ _ _ e.injective, hT, hA] at hn'
  have hi := positioned_test (e d) ((e.orderOf_eq d).trans hd) hn'
  apply (map_injective (f := e.toMonoidHom) e.injective)
  rw [map_inf _ _ _ e.injective, Subgroup.map_bot, hB]
  have hc : (B.map (MulAut.conj d⁻¹).toMonoidHom).map e.toMonoidHom =
      (B.map e.toMonoidHom).map (MulAut.conj (e d)⁻¹).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext x : 1
    change e (d⁻¹ * x * (d⁻¹)⁻¹) = (e d)⁻¹ * e x * ((e d)⁻¹)⁻¹
    simp only [map_mul, map_inv]
  rw [hc, hB]
  exact hi

/-- An elementary two-subgroup of a Sylow two-subgroup of S₅ has order at most four. -/
theorem elementary_card_le_four (T : Sylow 2 D) (B : Subgroup D)
    [IsElementaryAbelian 2 B]
    (hBT : B ≤ (T : Subgroup D)) : Nat.card B ≤ 4 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D T standardSylow
  let e := MulAut.conj g
  have hT : (T : Subgroup D).map e.toMonoidHom = eight :=
    congrArg (fun Q : Sylow 2 D => (Q : Subgroup D)) hg
  let : IsElementaryAbelian 2 (B.map e.toMonoidHom) := IsElementaryAbelian.map e.toMonoidHom
  have hB : B.map e.toMonoidHom ≤ eight := hT ▸ map_mono hBT
  have hc := positioned_card_le_four (B.map e.toMonoidHom) hB
  rwa [card_map_of_injective e.injective] at hc

end Theory.SpecificGroups.SymmetricFive.OuterFourIntersection
