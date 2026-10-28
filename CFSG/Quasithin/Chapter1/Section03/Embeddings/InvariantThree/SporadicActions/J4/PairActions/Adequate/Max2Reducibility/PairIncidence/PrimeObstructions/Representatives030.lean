module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Power
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
-- Intentional internal coupling to the checked witnesses in this certificate leaf.
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives030

/-!
# Order-6912 alternatives at indices 30 through 39

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
public theorem alternatives030 (i : Fin 10) :
    representative (Fin.ofNat 110 (30 + i.val)) ∈ involutionMatrixLineStabilizer ∨
    representative (Fin.ofNat 110 (30 + i.val)) ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative (Fin.ofNat 110 (30 + i.val))),
      x ^ 6912 ≠ 1 := by
  fin_cases i
  · refine Or.inr (Or.inr ⟨obstruction30 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 30)).pow_mem obstruction30_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction30_small_power obstruction30_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction31 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 31)).pow_mem obstruction31_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction31_small_power obstruction31_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction32 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 32)).pow_mem obstruction32_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction32_small_power obstruction32_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction33 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 33)).pow_mem obstruction33_mem 1, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction33_small_power obstruction33_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction34 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 34)).pow_mem obstruction34_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction34_small_power obstruction34_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction35 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 35)).pow_mem obstruction35_mem 1, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction35_small_power obstruction35_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction36 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 36)).pow_mem obstruction36_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction36_small_power obstruction36_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction37 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 37)).pow_mem obstruction37_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction37_small_power obstruction37_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction38 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 38)).pow_mem obstruction38_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction38_small_power obstruction38_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction39 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 39)).pow_mem obstruction39_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction39_small_power obstruction39_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
