module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Power
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
-- Intentional internal coupling to the checked witnesses in this certificate leaf.
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives080

/-!
# Order-6912 alternatives at indices 80 through 89

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
public theorem alternatives080 (i : Fin 10) :
    representative (Fin.ofNat 110 (80 + i.val)) ∈ involutionMatrixLineStabilizer ∨
    representative (Fin.ofNat 110 (80 + i.val)) ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative (Fin.ofNat 110 (80 + i.val))),
      x ^ 6912 ≠ 1 := by
  fin_cases i
  · refine Or.inr (Or.inr ⟨obstruction80 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 80)).pow_mem obstruction80_mem 3, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction80_small_power obstruction80_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction81 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 81)).pow_mem obstruction81_mem 1, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction81_small_power obstruction81_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction82 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 82)).pow_mem obstruction82_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction82_small_power obstruction82_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction83 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 83)).pow_mem obstruction83_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction83_small_power obstruction83_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction84 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 84)).pow_mem obstruction84_mem 3, ?_⟩)
    exact power6912_ne_one _ 11 (by decide +kernel)
      obstruction84_small_power obstruction84_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction85 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 85)).pow_mem obstruction85_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction85_small_power obstruction85_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction86 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 86)).pow_mem obstruction86_mem 3, ?_⟩)
    exact power6912_ne_one _ 11 (by decide +kernel)
      obstruction86_small_power obstruction86_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction87 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 87)).pow_mem obstruction87_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction87_small_power obstruction87_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction88 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 88)).pow_mem obstruction88_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction88_small_power obstruction88_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction89 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 89)).pow_mem obstruction89_mem 1, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction89_small_power obstruction89_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
