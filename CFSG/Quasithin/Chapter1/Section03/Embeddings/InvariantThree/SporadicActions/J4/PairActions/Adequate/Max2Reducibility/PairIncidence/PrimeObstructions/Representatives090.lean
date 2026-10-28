module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Power
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
-- Intentional internal coupling to the checked witnesses in this certificate leaf.
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives090

/-!
# Order-6912 alternatives at indices 90 through 99

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
public theorem alternatives090 (i : Fin 10) :
    representative (Fin.ofNat 110 (90 + i.val)) ∈ involutionMatrixLineStabilizer ∨
    representative (Fin.ofNat 110 (90 + i.val)) ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative (Fin.ofNat 110 (90 + i.val))),
      x ^ 6912 ≠ 1 := by
  fin_cases i
  · refine Or.inr (Or.inr ⟨obstruction90 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 90)).pow_mem obstruction90_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction90_small_power obstruction90_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction91 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 91)).pow_mem obstruction91_mem 3, ?_⟩)
    exact power6912_ne_one _ 11 (by decide +kernel)
      obstruction91_small_power obstruction91_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction92 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 92)).pow_mem obstruction92_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction92_small_power obstruction92_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction93 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 93)).pow_mem obstruction93_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction93_small_power obstruction93_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction94 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 94)).pow_mem obstruction94_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction94_small_power obstruction94_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction95 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 95)).pow_mem obstruction95_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction95_small_power obstruction95_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction96 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 96)).pow_mem obstruction96_mem 3, ?_⟩)
    exact power6912_ne_one _ 11 (by decide +kernel)
      obstruction96_small_power obstruction96_nonidentity
  · exact Or.inl r97_line
  · exact Or.inl r98_line
  · exact Or.inl r99_line


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
