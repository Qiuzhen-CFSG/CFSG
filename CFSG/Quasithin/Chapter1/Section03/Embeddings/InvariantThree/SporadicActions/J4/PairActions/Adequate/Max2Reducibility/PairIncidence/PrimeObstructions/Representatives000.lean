module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Power
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
-- Intentional internal coupling to the checked witnesses in this certificate leaf.
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives000

/-!
# Order-6912 alternatives at indices 0 through 9

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
public theorem alternatives000 (i : Fin 10) :
    representative (Fin.ofNat 110 (0 + i.val)) ∈ involutionMatrixLineStabilizer ∨
    representative (Fin.ofNat 110 (0 + i.val)) ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative (Fin.ofNat 110 (0 + i.val))),
      x ^ 6912 ≠ 1 := by
  fin_cases i
  · left
    exact involutionMatrixLineStabilizer.one_mem
  · exact Or.inl r1_line
  · refine Or.inr (Or.inr ⟨obstruction2 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 2)).pow_mem obstruction2_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction2_small_power obstruction2_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction3 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 3)).pow_mem obstruction3_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction3_small_power obstruction3_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction4 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 4)).pow_mem obstruction4_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction4_small_power obstruction4_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction5 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 5)).pow_mem obstruction5_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction5_small_power obstruction5_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction6 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 6)).pow_mem obstruction6_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction6_small_power obstruction6_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction7 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 7)).pow_mem obstruction7_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction7_small_power obstruction7_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction8 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 8)).pow_mem obstruction8_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction8_small_power obstruction8_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction9 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 9)).pow_mem obstruction9_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction9_small_power obstruction9_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
