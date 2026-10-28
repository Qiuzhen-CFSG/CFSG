module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalCertificate.Realization
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalCertificate.Checked
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalCertificate.Shape

/-!
# Finite bound for the candidate local presentation

A kernel-checked six-rule coset trace covers the local presented group by
1518 representatives over the cyclic subgroup on its second generator.
The fourth-power equation bounds that subgroup by four, giving 6072.
This does not yet bound the literal subgroup of the M24 presentation: that
transfer additionally requires the local relations to hold there.

Source and certificate reproduction: `source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound
open Subgroup.CosetWordCertificate LocalCertificate

/-- All signed transitions are actual equations in the smaller abstract group. -/
def localCosetCover :
    Subgroup.GeneratorCosetCover localCyclic localGenerator (Fin 1518) where
  repr i := definitions.repr certificateGenerator (survivor i)
  initial := 0
  initial_eq := by change definitions.repr certificateGenerator 0 = 1; simp
  step i a := by
    have h := all_hold certificate_valid _ (hlt i (a, true))
    rw [hshape] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨z, dest i (a, true), ?_⟩
    simpa only [eval_letter, embed, if_true, certificateGenerator_fin] using hz
  inv_step i a := by
    have h := all_hold certificate_valid _ (hlt i (a, false))
    rw [hshape] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨z, dest i (a, false), ?_⟩
    simpa only [eval_letter, embed, Bool.false_eq_true, if_false,
      certificateGenerator_fin] using hz

/-- Unconditional finiteness and bound for precisely the nine local relators. -/
theorem local_presentation_bound : Finite LocalPresented ∧ Nat.card LocalPresented ≤ 6072 := by
  obtain ⟨hf, hc⟩ := localCyclic_bound
  let : Finite localCyclic := hf
  obtain ⟨hf', hc'⟩ := localCosetCover.finite_card_le
    (PresentedGroup.closure_range_of (Set.range localRelator))
  refine ⟨hf', hc'.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 1518 hc

/-- Actual consumer of the local bound, with the missing source identities explicit. -/
theorem boundSubgroup_finite_card_le
    (hrel : ∀ i, eval boundGenerator (localRelatorLetters i) = 1) :
    Finite boundSubgroup ∧ Nat.card boundSubgroup ≤ 6072 :=
  boundSubgroup_finite_card_le_of_local hrel local_presentation_bound

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound
