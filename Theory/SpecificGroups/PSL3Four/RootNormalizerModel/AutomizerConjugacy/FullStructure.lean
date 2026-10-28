module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.Reduction
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure.Coverage

/-!
# Structural consequences of root-automorphism normal forms

Coverage by the explicit shift–diagonal–graph–field parameter map gives both
structural inputs required by the automizer-conjugacy reduction. Uniqueness
makes the full automorphism order 36 times a power of two, so the order-nine
torus is Sylow. For the normalizer bound, strip off the semilinear factor:
the remaining shift normalizes the inner–torus join and is therefore inner.

The geometric coverage theorem proves that every automorphism of the literal
root carrier has this normal form. Applying it to the preserved conditional
deductions gives the unconditional `torus_sylow` and
`normalizer_innerTorus_le` inputs to the automizer-conjugacy assembly.

Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.3, 46.14.
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
noncomputable section

/-- Normal-form coverage and uniqueness determine the automorphism order. -/
theorem automorphism_card_of_coverage (h : Function.Surjective normalForm) :
    Nat.card (MulAut Root) = Nat.card Shift * 36 := by
  rw [← Nat.card_congr (Equiv.ofBijective normalForm ⟨normalForm_injective, h⟩)]
  exact parameters_card

theorem torus_sylow_of_coverage (h : Function.Surjective normalForm) :
    ∃ T : Sylow 3 (MulAut Root), (T : Subgroup (MulAut Root)) = torus := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : IsPGroup 3 torus := IsPGroup.of_card (n := 2) torus_card
  have hi := torus.card_mul_index
  rw [torus_card, automorphism_card_of_coverage h] at hi
  have hie : torus.index = Nat.card Shift * 4 := by omega
  obtain ⟨n, hn⟩ := shift_card
  have hnd : ¬ 3 ∣ torus.index := by
    rw [hie, hn]
    exact (by decide : Nat.Prime 3).not_dvd_mul
      (fun hd => (by decide : ¬ 3 ∣ 2) ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3)) hd))
      (by decide)
  exact ⟨hp.toSylow hnd, rfl⟩

theorem normalizer_innerTorus_le_of_coverage (h : Function.Surjective normalForm) :
    normalizer (innerTorus : Set (MulAut Root)) ≤ inner ⊔ semilinear := by
  intro s hs
  obtain ⟨⟨l, a, g, f⟩, rfl⟩ := h s
  have ht := standardPart_mem a g f
  have htn := semilinear_le_normalizer_innerTorus ht
  have hl : shift l ∈ normalizer (innerTorus : Set (MulAut Root)) := by
    have hh := (normalizer (innerTorus : Set (MulAut Root))).mul_mem hs
      ((normalizer (innerTorus : Set (MulAut Root))).inv_mem htn)
    simpa only [normalForm, mul_inv_cancel_right] using hh
  exact mul_mem_sup ((shift_normalizer_iff l).mp hl) ht

end
end Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure

namespace Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy

/-- The diagonal torus is a Sylow three-subgroup of the full automorphism
group of the literal root carrier. -/
theorem torus_sylow :
    ∃ T : Sylow 3 (MulAut Root), (T : Subgroup (MulAut Root)) = torus :=
  FullStructure.torus_sylow_of_coverage FullStructure.normalForm_surjective

/-- Every automorphism normalizing the inner–torus join is a product of
an inner automorphism and a semilinear automorphism. -/
theorem normalizer_innerTorus_le :
    normalizer (innerTorus : Set (MulAut Root)) ≤ inner ⊔ semilinear :=
  FullStructure.normalizer_innerTorus_le_of_coverage FullStructure.normalForm_surjective

end Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy
