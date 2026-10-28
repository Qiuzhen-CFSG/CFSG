module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Power
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
-- Intentional internal coupling to the checked witnesses in this certificate leaf.
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives010

/-!
# Order-6912 alternatives at indices 10 through 19

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
public theorem alternatives010 (i : Fin 10) :
    representative (Fin.ofNat 110 (10 + i.val)) ∈ involutionMatrixLineStabilizer ∨
    representative (Fin.ofNat 110 (10 + i.val)) ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative (Fin.ofNat 110 (10 + i.val))),
      x ^ 6912 ≠ 1 := by
  fin_cases i
  · refine Or.inr (Or.inr ⟨obstruction10 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 10)).pow_mem obstruction10_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction10_small_power obstruction10_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction11 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 11)).pow_mem obstruction11_mem 1, ?_⟩)
    exact power6912_ne_one _ 11 (by decide +kernel)
      obstruction11_small_power obstruction11_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction12 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 12)).pow_mem obstruction12_mem 1, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction12_small_power obstruction12_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction13 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 13)).pow_mem obstruction13_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction13_small_power obstruction13_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction14 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 14)).pow_mem obstruction14_mem 3, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction14_small_power obstruction14_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction15 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 15)).pow_mem obstruction15_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction15_small_power obstruction15_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction16 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 16)).pow_mem obstruction16_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction16_small_power obstruction16_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction17 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 17)).pow_mem obstruction17_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction17_small_power obstruction17_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction18 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 18)).pow_mem obstruction18_mem 1, ?_⟩)
    exact power6912_ne_one _ 11 (by decide +kernel)
      obstruction18_small_power obstruction18_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction19 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 19)).pow_mem obstruction19_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction19_small_power obstruction19_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
