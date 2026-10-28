module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Disjoint
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Exclusion

/-!
# The center of the degree-eight Sylow quotient

Modulo the Klein-four product, an element is central exactly when it is even
and preserves each four-point block. Necessity is checked against a pair swap
and the block interchange; sufficiency is checked against the seven Sylow
generators and extended to their closure. The even pair subgroup consequently
maps onto the center of order two.

Source: Aschbacher–Smith, proof of 15.3.25 (I)–(IV), printed p.1133.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

def blockStabilizer : Subgroup Perm where
  carrier := {g | ∀ x, (g x).val / 4 = x.val / 4}
  one_mem' := by intro x; rfl
  mul_mem' := by intro g h hg hh x; exact (hg (h x)).trans (hh x)
  inv_mem' := by intro g hg x; simpa using (hg (g⁻¹ x)).symm

theorem blockCore_le_blockStabilizer : blockCore ≤ blockStabilizer := by
  intro g hg
  exact blockCore_preserves_each_half hg

private theorem blockStabilizer_iff (x : SylowGroup) :
    x.val ∈ blockStabilizer ↔ (x.val 0).val / 4 = 0 := by
  obtain ⟨i, hi⟩ := (mem_canonicalTwoSubgroup x).mp x.property
  have ht : ∀ i, (∀ y, (sylowWord i y).val / 4 = y.val / 4) ↔
      (sylowWord i 0).val / 4 = 0 := by decide +kernel
  rw [← hi]
  exact ht i

theorem quotientMap_eq_iff (x y : SylowGroup) :
    quotientMap x = quotientMap y ↔ x.val / y.val ∈ blockCore :=
  QuotientGroup.eq_iff_div_mem

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem center_test : ∀ i : Fin 128,
    (∃ k, coreWords k = (sylowWord i * pairSwap 8 0) / (pairSwap 8 0 * sylowWord i)) →
    (∃ k, coreWords k = (sylowWord i * halfSwap) / (halfSwap * sylowWord i)) →
    Equiv.Perm.sign (sylowWord i) = 1 ∧ (sylowWord i 0).val / 4 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem center_commutes : ∀ i : Fin 128,
    Equiv.Perm.sign (sylowWord i) = 1 → (sylowWord i 0).val / 4 = 0 →
    ∀ j : Fin 7, ∃ k,
      coreWords k = (sylowGenerators j * sylowWord i) / (sylowWord i * sylowGenerators j) := by decide +kernel

/-- The center consists exactly of the even elements preserving each block. -/
theorem quotientMap_mem_center_iff (x : SylowGroup) :
    quotientMap x ∈ Subgroup.center Quotient ↔
      x.val ∈ alternatingGroup (Fin 8) ∧ x.val ∈ blockStabilizer := by
  obtain ⟨i, hi⟩ := (mem_canonicalTwoSubgroup x).mp x.property
  constructor
  · intro hx
    have hcomm (y : SylowGroup) : x.val * y.val / (y.val * x.val) ∈ blockCore := by
      apply (quotientMap_eq_iff (x * y) (y * x)).mp
      simpa only [map_mul] using ((Subgroup.mem_center_iff.mp hx) (quotientMap y)).symm
    have h0 := hcomm ⟨pairSwap 8 0, sylowGenerators_mem 0⟩
    have h4 := hcomm ⟨halfSwap, sylowGenerators_mem 6⟩
    change (∃ k, coreWords k = _) at h0 h4
    rw [← hi] at h0 h4
    have ht := center_test i h0 h4
    refine ⟨?_, (blockStabilizer_iff x).mpr ?_⟩
    · change Equiv.Perm.sign x.val = 1
      simpa only [hi] using ht.1
    · simpa only [hi] using ht.2
  · rintro ⟨hs, hb⟩
    have hs' : Equiv.Perm.sign (sylowWord i) = 1 := hi ▸ hs
    have hb' := (blockStabilizer_iff x).mp hb
    rw [← hi] at hb'
    let C : Subgroup SylowGroup := (Subgroup.centralizer {quotientMap x}).comap quotientMap
    have hC : (canonicalSylow : Subgroup Perm) ≤ C.map (canonicalSylow : Subgroup Perm).subtype := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨j, rfl⟩
      refine ⟨⟨sylowGenerators j, sylowGenerators_mem j⟩, ?_, rfl⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      rw [← map_mul, ← map_mul, quotientMap_eq_iff]
      obtain ⟨k, hk⟩ := center_commutes i hs' hb' j
      refine ⟨k, ?_⟩
      change coreWords k = sylowGenerators j * x.val / (x.val * sylowGenerators j)
      simpa only [hi] using hk
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective sylowCore y
    obtain ⟨v, hv, he⟩ := hC z.property
    have hvz : v = z := Subtype.ext he
    subst v
    exact Subgroup.mem_centralizer_singleton_iff.mp hv

private theorem D_le_blockStabilizer : D 8 ≤ blockStabilizer := by
  have ht : ∀ i x, (dWords i x).val / 4 = x.val / 4 := by decide +kernel
  rintro x hx
  obtain ⟨i, rfl⟩ := (mem_D_iff x).mp hx
  exact ht i

theorem evenPart_inf_blockCore : evenPart 8 ⊓ blockCore = D 8 ⊓ blockCore := by
  ext x
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, blockCore_le_alternating h.2⟩, h.2⟩

theorem card_quotientImage_evenPart : Nat.card (quotientImage (evenPart 8)) = 2 := by
  have hc := card_inf_mul_card_quotientImage evenPart_le_canonicalSylow
  rw [evenPart_inf_blockCore, card_D_inf_blockCore, card_evenPart] at hc
  omega

set_option maxRecDepth 10000 in
private theorem central_word_cosets : ∀ i : Fin 128,
    Equiv.Perm.sign (sylowWord i) = 1 → (sylowWord i 0).val / 4 = 0 →
    ∃ j : Fin 16, Equiv.Perm.sign (dWords j) = 1 ∧
      ∃ k, coreWords k = dWords j / sylowWord i := by decide +kernel

/-- The canonical even pair subgroup maps onto the actual center. -/
theorem quotientImage_evenPart_eq_center :
    quotientImage (evenPart 8) = Subgroup.center Quotient := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (quotientMap_mem_center_iff x).mpr ⟨hx.2, D_le_blockStabilizer hx.1⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective sylowCore y
    obtain ⟨hs, hb⟩ := (quotientMap_mem_center_iff x).mp hy
    obtain ⟨i, hi⟩ := (mem_canonicalTwoSubgroup x).mp x.property
    have hs' : Equiv.Perm.sign (sylowWord i) = 1 := hi ▸ hs
    have hb' := (blockStabilizer_iff x).mp hb
    rw [← hi] at hb'
    obtain ⟨j, hj, k, hk⟩ := central_word_cosets i hs' hb'
    have hd : dWords j ∈ D 8 := (mem_D_iff _).mpr ⟨j, rfl⟩
    refine ⟨⟨dWords j, D_le_canonicalSylow hd⟩, ⟨hd, hj⟩, ?_⟩
    apply (quotientMap_eq_iff _ _).mpr
    exact ⟨k, by simpa only [hi] using hk⟩

theorem card_center : Nat.card (Subgroup.center Quotient) = 2 := by
  rw [← quotientImage_evenPart_eq_center]
  exact card_quotientImage_evenPart

theorem center_le_evenFour : Subgroup.center Quotient ≤ evenFour := by
  rw [← quotientImage_evenPart_eq_center]
  exact (quotientImage_le_evenFour_iff evenPart_le_canonicalSylow).mpr inf_le_right

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

end
