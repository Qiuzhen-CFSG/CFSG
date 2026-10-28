module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ProductCertificates.Data

/-!
# Soundness and sparse coverage of product certificates

Source: Parrott (1972), section 5, p.683; `source/README.md`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ProductCertificates

theorem certificateTest_sound (i : Fin 122) (e : Certificate)
    (ho : ∀ r : Fin 475, productTest (catalogueNs r) (catalogueK r) = true)
    (ht : certificateTest i e = true) :
    RepresentativeWitness i (certA e) (certB e) (certK e) := by
  simp only [certificateTest, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨⟨hk, hw₁⟩, hw₂⟩, hr₁⟩, hr₂⟩ := ht
  apply representativeWitness_of_productTests i (certA e) (certB e) (certK e)
    [(catalogueN₁ (certOrder e), word e.2.1), (catalogueN₂ (certOrder e), word e.2.2)]
  · intro nw hnw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnw
    rcases hnw with rfl | rfl
    · exact hw₁
    · exact hw₂
  · intro nw hnw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnw
    rcases hnw with rfl | rfl
    · exact recoveryTest_of_recoverTest _ _ _ _ hr₁
    · exact recoveryTest_of_recoverTest _ _ _ _ hr₂
  · simpa only [List.map_cons, List.map_nil, catalogueNs, hk] using ho (certOrder e)

theorem mask_testBit (es : List Certificate) (t : Nat) :
    (mask es).testBit t = true ↔
      ∃ e ∈ es, candidateIndex (certA e) (certB e) (certC e) = t := by
  induction es with
  | nil => simp [mask]
  | cons e es ih =>
    simp only [mask, List.foldr_cons, Nat.testBit_or, Bool.or_eq_true,
      Nat.testBit_two_pow, decide_eq_true_eq] at *
    rw [ih]
    simp

private theorem candidateIndex_injective (a b a' b' : Fin 32) (c c' : Fin 15)
    (h : candidateIndex a b c = candidateIndex a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  simp only [candidateIndex] at h
  have ha : a.val = a'.val := by omega
  have hb : b.val = b'.val := by omega
  have hc : c.val = c'.val := by omega
  exact ⟨Fin.ext ha, Fin.ext hb, Fin.ext hc⟩

theorem row_sound (i : Fin 122) (es : List Certificate)
    (ho : ∀ r : Fin 475, productTest (catalogueNs r) (catalogueK r) = true)
    (ht : es.all (certificateTest i) = true)
    (hm : mask es = productMasks (productSelector i)) :
    ∀ (a b : Fin 32) (c : Fin 15), witnessCase i a b c = .product →
      RepresentativeWitness i a b ⟨c.val + 3, by omega⟩ := by
  intro a b c h
  have hb : (productMasks (productSelector i)).testBit (candidateIndex a b c) = true := by
    simpa only [witnessCase, ite_eq_left_iff, ite_eq_iff, reduceCtorEq,
      and_false, or_false, imp_false, Bool.not_eq_false, not_not] using h
  rw [← hm, mask_testBit] at hb
  obtain ⟨e, he, hh⟩ := hb
  obtain ⟨ha, hb, hc⟩ := candidateIndex_injective _ _ _ _ _ _ hh
  have hw := certificateTest_sound i e ho (List.all_eq_true.mp ht e he)
  simpa only [certK, ha, hb, hc] using hw
end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ProductCertificates
