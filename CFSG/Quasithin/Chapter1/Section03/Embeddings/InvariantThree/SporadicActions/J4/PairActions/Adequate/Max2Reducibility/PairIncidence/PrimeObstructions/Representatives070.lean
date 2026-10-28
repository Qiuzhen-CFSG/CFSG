module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Power
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
-- Intentional internal coupling to the checked witnesses in this certificate leaf.
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives070

/-!
# Order-6912 alternatives at indices 70 through 79

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
public theorem alternatives070 (i : Fin 10) :
    representative (Fin.ofNat 110 (70 + i.val)) ∈ involutionMatrixLineStabilizer ∨
    representative (Fin.ofNat 110 (70 + i.val)) ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative (Fin.ofNat 110 (70 + i.val))),
      x ^ 6912 ≠ 1 := by
  fin_cases i
  · refine Or.inr (Or.inr ⟨obstruction70 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 70)).pow_mem obstruction70_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction70_small_power obstruction70_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction71 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 71)).pow_mem obstruction71_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction71_small_power obstruction71_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction72 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 72)).pow_mem obstruction72_mem 1, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction72_small_power obstruction72_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction73 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 73)).pow_mem obstruction73_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction73_small_power obstruction73_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction74 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 74)).pow_mem obstruction74_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction74_small_power obstruction74_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction75 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 75)).pow_mem obstruction75_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction75_small_power obstruction75_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction76 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 76)).pow_mem obstruction76_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction76_small_power obstruction76_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction77 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 77)).pow_mem obstruction77_mem 1, ?_⟩)
    exact power6912_ne_one _ 11 (by decide +kernel)
      obstruction77_small_power obstruction77_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction78 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 78)).pow_mem obstruction78_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction78_small_power obstruction78_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction79 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 79)).pow_mem obstruction79_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction79_small_power obstruction79_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
