module

public import BenderSuzuki.External.Huppert.II.theorem_8_3_split
public import Theory.GroupTheory.OddInvolutionNormalizer

/-!
# Odd torus normalizers

Reflection normalizers have two cosets: the torus and a coset consisting of
involutions. Thus odd elements of a subgroup normalizer belong to the torus,
and involutions invert it. These facts transport through actual group
equivalences. The concrete producers are Huppert II.8.3 and II.8.4; the
consumer is the characteristic-two PSL₂ analysis for GLS4, 2.17.5.
-/

public section

open Subgroup
open scoped Pointwise IsMulCommutative
namespace BenderSuzuki.MatrixGroups.EvenOddTori
variable {G K : Type*} [Group G] [Group K]

structure ReflectionData (T : Subgroup G) : Prop where
  cyclic : IsCyclic T
  odd : Odd (Nat.card T)
  reflection : ∃ w : G, w ∈ normalizer T ∧ w ∉ T ∧ w * w = 1 ∧
    (∀ x ∈ T, w * x * w⁻¹ = x⁻¹) ∧
    ∀ R : Subgroup G, R ≤ T → R ≠ ⊥ → normalizer R = T ⊔ zpowers w

namespace ReflectionData
variable {T R : Subgroup G} (d : ReflectionData T)
include d

lemma outside_sq (hRT : R ≤ T) (hR : R ≠ ⊥) {g : G}
    (hg : g ∈ normalizer R) (hout : g ∉ T) : g ^ 2 = 1 := by
  classical
  obtain ⟨w, hwN, hwT, hww, hinv, hN⟩ := d.reflection
  have hw2 : w ^ 2 = 1 := by simpa [pow_two] using hww
  have hw1 : w ≠ 1 := fun h => hwT (h ▸ T.one_mem)
  have ho : orderOf w = 2 := orderOf_eq_prime hw2 hw1
  have hf : IsOfFinOrder w := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hw2⟩
  rw [hN R hRT hR] at hg
  have hprod : g ∈ (T : Set G) * (zpowers w : Set G) := by
    rwa [← coe_mul_of_right_le_normalizer_left T (zpowers w) (zpowers_le.mpr hwN)]
  obtain ⟨a, ha, b, hb, rfl⟩ := hprod
  change b ∈ zpowers w at hb
  rw [hf.mem_zpowers_iff_mem_range_orderOf, ho] at hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  have hi2 := Finset.mem_range.mp hi
  have hic : i = 0 ∨ i = 1 := by omega
  rcases hic with rfl | rfl
  · exact (hout (by simpa using ha)).elim
  · simp only [pow_one]
    have hwa : w * a = a⁻¹ * w := by
      have h := congrArg (fun x => x * w) (hinv a ha)
      simpa [mul_assoc] using h
    calc
      (a * w) ^ 2 = a * (w * a) * w := by simp [pow_two, mul_assoc]
      _ = a * (a⁻¹ * w) * w := by rw [hwa]
      _ = 1 := by simp [← mul_assoc, hww]

lemma odd_mem (hRT : R ≤ T) (hR : R ≠ ⊥) {g : G}
    (hg : g ∈ normalizer R) (ho : Odd (orderOf g)) : g ∈ T := by
  by_contra hout
  have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (d.outside_sq hRT hR hg hout)
  have he : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes ho.coprime_two_right dvd_rfl hd
  exact hout ((orderOf_eq_one_iff.mp he) ▸ T.one_mem)

lemma involution_inverts (hRT : R ≤ T) (hR : R ≠ ⊥) {t : G}
    (ht : orderOf t = 2) (htN : t ∈ normalizer R) :
    ∀ x ∈ T, t * x * t⁻¹ = x⁻¹ := by
  classical
  obtain ⟨w, hwN, hwT, hww, hinv, hN⟩ := d.reflection
  have htT : t ∉ T := by
    intro h
    have hd := orderOf_dvd_natCard (⟨t, h⟩ : T)
    rw [Subgroup.orderOf_mk, ht] at hd
    exact d.odd.not_two_dvd_nat hd
  have hw2 : w ^ 2 = 1 := by simpa [pow_two] using hww
  have hw1 : w ≠ 1 := fun h => hwT (h ▸ T.one_mem)
  have ho : orderOf w = 2 := orderOf_eq_prime hw2 hw1
  have hf : IsOfFinOrder w := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hw2⟩
  rw [hN R hRT hR] at htN
  have hprod : t ∈ (T : Set G) * (zpowers w : Set G) := by
    rwa [← coe_mul_of_right_le_normalizer_left T (zpowers w) (zpowers_le.mpr hwN)]
  obtain ⟨a, ha, b, hb, rfl⟩ := hprod
  change b ∈ zpowers w at hb
  rw [hf.mem_zpowers_iff_mem_range_orderOf, ho] at hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  have hi2 := Finset.mem_range.mp hi
  have hic : i = 0 ∨ i = 1 := by omega
  rcases hic with rfl | rfl
  · exact (htT (by simpa using ha)).elim
  · intro x hx
    let := d.cyclic
    have hac : a * x⁻¹ = x⁻¹ * a :=
      congrArg Subtype.val (mul_comm (⟨a, ha⟩ : T) (⟨x⁻¹, T.inv_mem hx⟩ : T))
    calc
      (a * w ^ 1) * x * (a * w ^ 1)⁻¹ = a * (w * x * w⁻¹) * a⁻¹ := by group
      _ = a * x⁻¹ * a⁻¹ := by rw [hinv x hx]
      _ = x⁻¹ := by rw [hac]; group

lemma map (e : G ≃* K) : ReflectionData (T.map e.toMonoidHom) := by
  classical
  let := d.cyclic
  refine ⟨isCyclic_of_surjective (T.equivMapOfInjective e.toMonoidHom e.injective)
    (T.equivMapOfInjective e.toMonoidHom e.injective).surjective,
    by simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using d.odd, ?_⟩
  obtain ⟨w, hwN, hwT, hww, hinv, hN⟩ := d.reflection
  refine ⟨e w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_equiv_normalizer_eq]
    exact mem_map.mpr ⟨w, hwN, rfl⟩
  · simpa only [mem_map_equiv, e.symm_apply_apply] using hwT
  · rw [← map_mul, hww, map_one]
  · rintro x ⟨y, hy, rfl⟩
    simpa using congrArg e (hinv y hy)
  · intro S hS hSne
    let R := S.map e.symm.toMonoidHom
    have hRT : R ≤ T := by
      rintro x ⟨y, hy, rfl⟩
      exact (mem_map_equiv.mp (hS hy))
    have hRne : R ≠ ⊥ := by
      intro h
      apply hSne
      apply eq_bot_iff.mpr
      intro y hy
      have hh : e.symm y ∈ R := mem_map.mpr ⟨y, hy, rfl⟩
      rw [h, mem_bot] at hh
      exact e.symm.injective (hh.trans (map_one e.symm).symm)
    have hmap : R.map e.toMonoidHom = S := by
      exact (map_symm_eq_iff_map_eq R).mp rfl
    rw [← hmap, ← map_equiv_normalizer_eq, hN R hRT hRne, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl

end ReflectionData
end BenderSuzuki.MatrixGroups.EvenOddTori
