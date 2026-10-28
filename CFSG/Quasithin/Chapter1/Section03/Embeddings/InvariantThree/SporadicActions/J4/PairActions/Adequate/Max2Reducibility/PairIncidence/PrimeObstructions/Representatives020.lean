module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Power
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
-- Intentional internal coupling to the checked witnesses in this certificate leaf.
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives020

/-!
# Order-6912 alternatives at indices 20 through 29

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
public theorem alternatives020 (i : Fin 10) :
    representative (Fin.ofNat 110 (20 + i.val)) ∈ involutionMatrixLineStabilizer ∨
    representative (Fin.ofNat 110 (20 + i.val)) ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative (Fin.ofNat 110 (20 + i.val))),
      x ^ 6912 ≠ 1 := by
  fin_cases i
  · refine Or.inr (Or.inr ⟨obstruction20 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 20)).pow_mem obstruction20_mem 3, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction20_small_power obstruction20_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction21 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 21)).pow_mem obstruction21_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction21_small_power obstruction21_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction22 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 22)).pow_mem obstruction22_mem 3, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction22_small_power obstruction22_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction23 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 23)).pow_mem obstruction23_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction23_small_power obstruction23_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction24 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 24)).pow_mem obstruction24_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction24_small_power obstruction24_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction25 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 25)).pow_mem obstruction25_mem 3, ?_⟩)
    exact power6912_ne_one _ 11 (by decide +kernel)
      obstruction25_small_power obstruction25_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction26 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 26)).pow_mem obstruction26_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction26_small_power obstruction26_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction27 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 27)).pow_mem obstruction27_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction27_small_power obstruction27_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction28 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 28)).pow_mem obstruction28_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction28_small_power obstruction28_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction29 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 29)).pow_mem obstruction29_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction29_small_power obstruction29_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
