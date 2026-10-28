module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Power
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
-- Intentional internal coupling to the checked witnesses in this certificate leaf.
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives060

/-!
# Order-6912 alternatives at indices 60 through 69

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
public theorem alternatives060 (i : Fin 10) :
    representative (Fin.ofNat 110 (60 + i.val)) ∈ involutionMatrixLineStabilizer ∨
    representative (Fin.ofNat 110 (60 + i.val)) ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative (Fin.ofNat 110 (60 + i.val))),
      x ^ 6912 ≠ 1 := by
  fin_cases i
  · refine Or.inr (Or.inr ⟨obstruction60 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 60)).pow_mem obstruction60_mem 3, ?_⟩)
    exact power6912_ne_one _ 11 (by decide +kernel)
      obstruction60_small_power obstruction60_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction61 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 61)).pow_mem obstruction61_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction61_small_power obstruction61_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction62 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 62)).pow_mem obstruction62_mem 3, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction62_small_power obstruction62_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction63 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 63)).pow_mem obstruction63_mem 2, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction63_small_power obstruction63_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction64 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 64)).pow_mem obstruction64_mem 1, ?_⟩)
    exact power6912_ne_one _ 5 (by decide +kernel)
      obstruction64_small_power obstruction64_nonidentity
  · exact Or.inr (Or.inl r65_second)
  · refine Or.inr (Or.inr ⟨obstruction66 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 66)).pow_mem obstruction66_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction66_small_power obstruction66_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction67 ^ 1,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 67)).pow_mem obstruction67_mem 1, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction67_small_power obstruction67_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction68 ^ 2,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 68)).pow_mem obstruction68_mem 2, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction68_small_power obstruction68_nonidentity
  · refine Or.inr (Or.inr ⟨obstruction69 ^ 3,
      (baseSubgroup ⊔ Subgroup.zpowers (representative 69)).pow_mem obstruction69_mem 3, ?_⟩)
    exact power6912_ne_one _ 7 (by decide +kernel)
      obstruction69_small_power obstruction69_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
