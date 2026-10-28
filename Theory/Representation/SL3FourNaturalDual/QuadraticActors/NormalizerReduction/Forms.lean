module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Centralizer
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Model
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Forms.Summands
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Forms.NaturalBlock
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Forms.DualBlock

/-!
# Assembly of standard forms for the binary SL₃(4) normalizer

The summand dichotomy reduces the full normalizer to operators preserving the
two coordinate summands. This module assembles an explicit semilinear matrix
formula for the natural block and the corresponding scalar contragredient
formula for the dual block. The same witnesses give the exchanging form after
composition with the concrete graph swap.

The natural block's matrix and field automorphism are constructed by conjugating
the scalar commutant. The invariant natural--dual pairing then determines the
dual block with the same field automorphism and an independent nonzero scalar.
`hasStandardForm_of_mem_normalizer` combines these proved block classifications
to give unconditional coverage of the actual binary normalizer.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed p.955 (PDF p.972), natural-plus-dual SL₃(4) case.
-/

public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction

/-- Assembling the two actual diagonal formulas gives the preserving standard form. -/
theorem standardPair_of_blocks (f : BinaryGL) (hp : PreservesSummands f)
    (M : Matrix.GeneralLinearGroup (Fin 3) F) (c : Fˣ) (σ : F ≃+* F)
    (hnat : ∀ w : W, firstBlock f w = M.val.mulVec (σ ∘ w))
    (hdual : ∀ w : W, secondBlock f w =
      (c : F) • (M⁻¹).val.transpose.mulVec (σ ∘ w)) :
    ∀ v : V, f v = standardPair M c σ v := by
  intro v
  rw [preservesSummands_apply f hp]
  exact Prod.ext (hnat v.1) (hdual v.2)

/-- Coverage for preserving operators suffices for all normalizer elements. -/
theorem hasStandardForm_of_preserving_coverage
    (hpres : ∀ f : BinaryGL, f ∈ normalizer → PreservesSummands f →
      ∃ (M : Matrix.GeneralLinearGroup (Fin 3) F) (c : Fˣ) (σ : F ≃+* F),
        ∀ v : V, f v = standardPair M c σ v)
    (f : BinaryGL) (hf : f ∈ normalizer) : HasStandardForm f := by
  rcases normalizer_summand_dichotomy f hf with hp | hp
  · obtain ⟨M, c, σ, h⟩ := hpres f hf hp
    exact ⟨M, c, σ, Or.inl h⟩
  · obtain ⟨M, c, σ, h⟩ := hpres (f * graphSwap)
      (normalizer.mul_mem hf graphSwap_mem_normalizer) hp
    refine ⟨M, c, σ, Or.inr (fun v => ?_)⟩
    exact h (v.2, v.1)

/-- The two independent block calculations suffice for the full normalizer
classification. Their hypotheses are discharged in `hasStandardForm_of_mem_normalizer`. -/
theorem hasStandardForm_of_block_classification
    (hnatural : ∀ f : BinaryGL, f ∈ normalizer → PreservesSummands f →
      ∃ (M : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F),
        ∀ w : W, firstBlock f w = M.val.mulVec (σ ∘ w))
    (hdual : ∀ f : BinaryGL, f ∈ normalizer → PreservesSummands f →
      ∀ (M : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F),
        (∀ w : W, firstBlock f w = M.val.mulVec (σ ∘ w)) →
        ∃ c : Fˣ, ∀ w : W, secondBlock f w =
          (c : F) • (M⁻¹).val.transpose.mulVec (σ ∘ w))
    (f : BinaryGL) (hf : f ∈ normalizer) : HasStandardForm f := by
  apply hasStandardForm_of_preserving_coverage _ f hf
  intro u hu hp
  obtain ⟨M, σ, hM⟩ := hnatural u hu hp
  obtain ⟨c, hc⟩ := hdual u hu hp M σ hM
  exact ⟨M, c, σ, standardPair_of_blocks u hp M c σ hM hc⟩

/-- Every binary operator normalizing the actual natural-plus-dual SL₃(4)
component has one of the explicit semilinear coordinate forms, retaining an
arbitrary invertible natural matrix and an independent nonzero dual scalar. -/
theorem hasStandardForm_of_mem_normalizer (f : BinaryGL) (hf : f ∈ normalizer) :
    HasStandardForm f :=
  hasStandardForm_of_block_classification naturalBlock_standard dualBlock_standard f hf


end Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
