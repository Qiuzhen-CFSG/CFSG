module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Reduction
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.Forest
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.FiniteFusion
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.Words
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.WordCoverage

/-!
# Exhaustive conjugacy coverage of Held involutions

An involution generates a two-subgroup and hence belongs to a Sylow
two-subgroup. The published four-word representative is a proved two-group
and is self-normalizing, so it is Sylow. Sylow conjugacy then transports
coverage of its involutions to all of Held.

The conditional reductions below isolate self-normalization, surjectivity
of the published 1024 binary words, and finite word fusion. The final theorem
discharges all three using their checked certificates. Thus every involution
of the actual Held carrier is conjugate to `a` or `max5First ^ 4`, with no
extra hypotheses. The module imports the inner-row reduction directly so
that the inner-row assembly may import this result.

Source: GLS3 Table 5.3p, interpreted on printed pp.260–261, and the actual
ATLAS HeG1-p2058B0 degree-2058 carrier. Only the literal words and their
surjectivity are used from IntrinsicEnumeration; no maximal-normalizer
catalogue is used.
-/

public section

namespace Held.InvolutionFixedData.Coverage
open Subgroup LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
open scoped Pointwise

/-- Coverage in the fixed representative suffices once it is self-normalizing.
The two-group premise is discharged by its existing kernel-checked proof. -/
theorem innerInvolutionCoverage_of_representative
    (hn : normalizer (representative : Set He) = representative)
    (hlocal : ∀ y : representative, orderOf y.val = 2 → IsCovered y.val) :
    InnerInvolutionCoverage := by
  obtain ⟨P, hP⟩ := exists_representative_sylow representative_isPGroup hn
  intro g hg
  have hgp : IsPGroup 2 (zpowers g) :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one, Nat.card_zpowers] using hg)
  obtain ⟨S, hS⟩ := hgp.exists_le_sylow
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq He P S
  have hmem := hS (mem_zpowers g)
  rw [← hd] at hmem
  change g ∈ (P : Subgroup He).map (MulAut.conj d).toMonoidHom at hmem
  rw [hP] at hmem
  obtain ⟨y, hy, hyconj⟩ := hmem
  have hyorder : orderOf y = 2 := by
    rw [← orderOf_injective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective y,
      hyconj, hg]
  exact hyconj ▸ (hlocal ⟨y, hy⟩ hyorder).conj d

/-- The precise three inputs for final assembly: self-normalization of the
two-group, exhaustive binary words, and conjugacy coverage of those words. -/
theorem innerInvolutionCoverage_of_normalForms
    (hn : normalizer (representative : Set He) = representative)
    (hwords : Function.Surjective normalForm)
    (hfusion : ∀ n : Fin 1024, orderOf (normalForm n).val = 2 →
      IsCovered (normalForm n).val) : InnerInvolutionCoverage := by
  apply innerInvolutionCoverage_of_representative hn
  intro y hy
  obtain ⟨n, rfl⟩ := hwords y
  exact hfusion n hy

/-- Every involution in the actual degree-2058 Held carrier is conjugate to
`a` or `max5First ^ 4`. Self-normalization, exhaustive word coverage, and
finite fusion are all discharged; no simplicity or perfectness premise is
needed. -/
theorem innerInvolutionCoverage : InnerInvolutionCoverage :=
  innerInvolutionCoverage_of_normalForms InnerNormalizer.normalizer_eq
    normalForm_surjective normalForm_isCovered

end Held.InvolutionFixedData.Coverage
