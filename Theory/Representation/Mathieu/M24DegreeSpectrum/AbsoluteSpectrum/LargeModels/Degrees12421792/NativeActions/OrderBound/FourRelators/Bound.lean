module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.FourRelators.Certificate.Realization
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.FourRelators.Certificate.Checked
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.FourRelators.Certificate.Shape

/-!
# Finite bound from the first four max8 relations

A kernel-checked six-rule coset trace covers the local presented group by
3036 representatives over the cyclic subgroup on its second generator.
The fourth-power equation bounds that subgroup by four, giving 12144.
The literal subgroup bound retains exactly the quartic and first mixed
identities. `Source` supplies the proved quartic identity and uses this bound
with an outer cover and the trivial native multiplier.

The certificate retains 54408 elementary deductions on 10064 acyclic
representative definitions. All 12144 signed transitions are checked; only
the second generator is allowed as a subgroup loop. The 78 relator variants
are inverses and rotations of the four exact words from `LocalPresentation`.
`Certificate.Realization` checks their literal agreement with those words.

Source: John Bray, ATLAS M24G1-P1 and M24G1-max8W1, attributed to R. A. Wilson
et al., ATLAS of Finite Group Representations. The unchanged original data
are retained in `../source/`. The original six-rule producer and emitter are
adapted under the repository Apache-2.0 license, with their attribution
preserved in `source/Produce.py` and `source/Generate.py`. Reproduce with
`python3 <this-directory>/source/Generate.py --check`; `source/local-cover.json`
is untrusted input to that emitter, whose Lean output proves every deduction.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.FourRelators
open Subgroup.CosetWordCertificate Certificate

/-- All signed transitions are actual equations in the smaller abstract group. -/
def localCosetCover :
    Subgroup.GeneratorCosetCover localCyclic localGenerator (Fin 3036) where
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

/-- Unconditional finiteness and bound for precisely the first four local relators. -/
theorem local_presentation_bound : Finite Presented ∧ Nat.card Presented ≤ 12144 := by
  obtain ⟨hf, hc⟩ := localCyclic_bound
  let : Finite localCyclic := hf
  obtain ⟨hf', hc'⟩ := localCosetCover.finite_card_le
    (PresentedGroup.closure_range_of (Set.range relator))
  refine ⟨hf', hc'.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 3036 hc

/-- The first mixed identity, together with the quartic identity, bounds the
literal subgroup by twice 6072. No cycle-power equation is needed. -/
theorem boundSubgroup_bound (hq : LocalRelations.QuarticRelation)
    (hf : LocalRelations.Mixed.FirstRelation) :
    Finite boundSubgroup ∧ Nat.card boundSubgroup ≤ 12144 := by
  let : Finite Presented := local_presentation_bound.1
  have hs := (toUniversal hq hf).rangeRestrict_surjective
  have hfin : Finite (toUniversal hq hf).range := Finite.of_surjective _ hs
  have hc : Nat.card (toUniversal hq hf).range ≤ 12144 :=
    (Nat.card_le_card_of_surjective _ hs).trans local_presentation_bound.2
  rw [toUniversal_range] at hfin hc
  exact ⟨hfin, hc⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.FourRelators
