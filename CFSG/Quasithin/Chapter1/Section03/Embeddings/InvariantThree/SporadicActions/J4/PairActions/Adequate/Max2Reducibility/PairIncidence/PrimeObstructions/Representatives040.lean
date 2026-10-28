module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Power
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
-- Intentional internal coupling to the checked witnesses in this certificate leaf.
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives040

/-!
# Order-6912 alternatives at indices 40 through 49

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
public theorem alternatives040 (i : Fin 10) :
    representative (Fin.ofNat 110 (40 + i.val)) ∈ involutionMatrixLineStabilizer ∨
    representative (Fin.ofNat 110 (40 + i.val)) ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative (Fin.ofNat 110 (40 + i.val))),
      x ^ 6912 ≠ 1 := by
  fin_cases i
  · refine Or.inr (Or.inr ⟨obstruction40 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 40)).pow_mem obstruction40_mem 3, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction40_small_power obstruction40_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction41 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 41)).pow_mem obstruction41_mem 3, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction41_small_power obstruction41_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction42 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 42)).pow_mem obstruction42_mem 1, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction42_small_power obstruction42_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction43 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 43)).pow_mem obstruction43_mem 1, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction43_small_power obstruction43_nonidentity
  · exact Or.inl r44_line
  · exact Or.inl r45_line
  · refine Or.inr (Or.inr ⟨obstruction46 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 46)).pow_mem obstruction46_mem 3, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction46_small_power obstruction46_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction47 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 47)).pow_mem obstruction47_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction47_small_power obstruction47_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction48 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 48)).pow_mem obstruction48_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction48_small_power obstruction48_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction49 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 49)).pow_mem obstruction49_mem 3, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction49_small_power obstruction49_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
