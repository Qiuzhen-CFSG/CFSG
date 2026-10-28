module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Generation
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.SectionStructure.SourceAction
public import Mathlib.RepresentationTheory.Coinvariants
/-!
# Lifting the L₁ difference calculation through the source line

The action-difference space on the actual U_H/V₁ is the image of
[U_H,L₁]. The source identity V₁=[V₃,O₂(L₁)] puts the entire kernel
inside that commutator subgroup. Full difference generation therefore
lifts to U_H=[U_H,L₁], retaining the line rather than dropping it.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.6(4), printed p.948 (PDF p.965).
The full difference-generation input remains a separate calculation.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]

/-- Full difference generation on U_H/V₁ lifts using the literal source
line commutator, with normality only inside the actual numerator. -/
theorem UH_eq_commutator_of_coinvariants
    (H L₁ V₁ V₃ : Subgroup G) (hL₁H : L₁ ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) U)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hgen : Coinvariants.ker (ρ.comp ((QuotientGroup.mk' (pCore 2 H)).comp
      (inclusion hL₁H))) = ⊤)
    (hline : V₁ = ⁅V₃, L₁.pCoreIn 2⁆) :
    Source.UH H V₃ = ⁅Source.UH H V₃, L₁⁆ := by
  have hline' : V₁ ≤ ⁅Source.UH H V₃, L₁⁆ := by
    rw [hline]
    exact commutator_mono (le_conjugateSpanBy V₃ H) (pCoreIn_le 2 L₁)
  have hC : Coinvariants.ker (ρ.comp ((QuotientGroup.mk' (pCore 2 H)).comp
      (inclusion hL₁H))) ≤ s.image ⁅Source.UH H V₃, L₁⁆ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨l, v⟩, rfl⟩
    obtain ⟨u, rfl⟩ := s.surjective (Multiplicative.ofAdd v)
    change ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hL₁H l)) (s.quotient u).toAdd -
      (s.quotient u).toAdd ∈ _
    rw [s.displacement]
    refine ⟨_, ?_, rfl⟩
    rw [commutator_comm]
    exact commutator_mem_commutator l.property u.property
  apply le_antisymm _ (le_normalizer_iff_commutator_le_left.mp
    (hL₁H.trans (le_normalizer_conjugateSpanBy V₃ H)))
  intro u hu
  apply (s.quotient_mem_image_iff _ hline' ⟨u, hu⟩).mp
  exact hC (hgen.symm ▸ Submodule.mem_top)
end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

end
