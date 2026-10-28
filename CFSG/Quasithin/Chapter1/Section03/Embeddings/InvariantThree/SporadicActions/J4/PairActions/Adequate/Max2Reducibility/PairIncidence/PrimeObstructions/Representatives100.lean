module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Power
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
-- Intentional internal coupling to the checked witnesses in this certificate leaf.
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives100

/-!
# Order-6912 alternatives at indices 100 through 109

This adapter reuses the original private nonidentity and small-power proofs.
The original 2304th-power inequality alone would not suffice. Keeping the
private import local to this block preserves the public certificate interface
and avoids loading all private matrix implementations into one module.

Source: Aschbacher--Smith, Proposition 1.3.4, printed p.511/PDF p.528;
word provenance is in FiniteIncidence/Obstructions/source/README.md.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
open FiniteIncidence FiniteIncidence.ObstructionCertificate

/-- The original witnesses, with their coprime-power argument applied to 6912. -/
public theorem alternatives100 (i : Fin 10) :
    representative (Fin.ofNat 110 (100 + i.val)) ∈ involutionMatrixLineStabilizer ∨
    representative (Fin.ofNat 110 (100 + i.val)) ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative (Fin.ofNat 110 (100 + i.val))),
      x ^ 6912 ≠ 1 := by
  fin_cases i
  · exact Or.inl r100_line
  · refine Or.inr (Or.inr ⟨obstruction101 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 101)).pow_mem obstruction101_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction101_small_power obstruction101_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction102 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 102)).pow_mem obstruction102_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction102_small_power obstruction102_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction103 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 103)).pow_mem obstruction103_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction103_small_power obstruction103_nonidentity
  · exact Or.inr (Or.inl r104_second)
  · refine Or.inr (Or.inr ⟨obstruction105 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 105)).pow_mem obstruction105_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction105_small_power obstruction105_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction106 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 106)).pow_mem obstruction106_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction106_small_power obstruction106_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction107 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 107)).pow_mem obstruction107_mem 1, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction107_small_power obstruction107_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction108 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 108)).pow_mem obstruction108_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction108_small_power obstruction108_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction109 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 109)).pow_mem obstruction109_mem 1, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction109_small_power obstruction109_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
