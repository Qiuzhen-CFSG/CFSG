module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Proper
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Data
public import Theory.GroupTheory.PGroup.ElementaryNormalizer

/-!
# Six elementary normalizers suffice for the fixed Rudvalis local cover

Given U normal inside the fixed subgroup, Ω₁(Z(U)) is a nontrivial elementary
subgroup normal there, and its ambient normalizer contains N(U). Thus a
complete catalogue of normal elementary subgroups reduces the local cover to
six ambient normalizer containments. Properness of the two ATLAS candidates
then turns maximality into an actual multiplicative equivalence.

The three propositions below are explicit, independent proof obligations on
the fixed words. The theorem is a conditional reduction, not the unconditional
Rudvalis local cover. Its assembly owner must construct all three witnesses.
No ambient Sylow fact, full model order, radical enumeration, or candidate
cardinality bound is assumed.

Source: the characteristic-center reduction for finite p-groups; the
Rudvalis application is the [Asc86b] analysis cited in Aschbacher--Smith,
printed p.511 (PDF p.528), with candidate structures in GLS3 Table 5.3r.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover

open Subgroup

/-- The fixed word subgroup is the image of a Sylow subgroup of max4.
This asserts Sylow status only inside max4. -/
@[expose] public def IntrinsicSylow : Prop :=
  ∃ S : Sylow 2 max4, (S : Subgroup max4).map max4.subtype = localP

/-- The intrinsic Sylow certificate supplies the two-group hypothesis for
the independent elementary catalogue calculation. -/
public theorem IntrinsicSylow.isPGroup (h : IntrinsicSylow) : IsPGroup 2 localP := by
  obtain ⟨S, hS⟩ := h
  rw [← hS]
  exact S.isPGroup'.map max4.subtype

/-- Completeness of the six candidates for nontrivial normal elementary
subgroups of the fixed word subgroup. The two inclusions express relative
normality; there is no ambient-normality hypothesis. -/
@[expose] public def ElementaryCatalogue : Prop :=
  ∀ E : Subgroup Model, E ≠ ⊥ → E ≤ localP →
    localP ≤ normalizer (E : Set Model) → IsElementaryAbelian 2 E →
    ∃ i : Fin 6, E = elementary i

/-- Ambient normalizer containments for the six explicit candidates.
Conjugators are actual elements of the preserved Rudvalis carrier. -/
@[expose] public def ElementaryNormalizerCover : Prop :=
  ∀ i : Fin 6,
    (∃ g : Model, normalizer (elementary i : Set Model) ≤
      max4.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : Model, normalizer (elementary i : Set Model) ≤
      max6.map (MulAut.conj g).toMonoidHom)

/-- The four proposed containments in the unchanged fourth ATLAS candidate.
The remaining indices, zero and five, have separate max6 certificates. -/
@[expose] public def Max4NormalizerBounds : Prop :=
  ∀ i : Fin 6, i ≠ 0 → i ≠ 5 → normalizer (elementary i : Set Model) ≤ max4

/-- The two remaining normalizers lie in actual conjugates of max6. -/
@[expose] public def Max6NormalizerBounds : Prop :=
  ∀ i : Fin 6, i = 0 ∨ i = 5 → ∃ g : Model,
    normalizer (elementary i : Set Model) ≤ max6.map (MulAut.conj g).toMonoidHom

/-- Assemble the two independent ambient normalizer calculations. -/
public theorem elementaryNormalizerCover_of_bounds
    (h4 : Max4NormalizerBounds) (h6 : Max6NormalizerBounds) :
    ElementaryNormalizerCover := by
  intro i
  by_cases h : i = 0 ∨ i = 5
  · exact Or.inr (h6 i h)
  · refine Or.inl ⟨1, ?_⟩
    have hId : (MulAut.conj (1 : Model)).toMonoidHom = MonoidHom.id Model := by
      ext x
      simp
    rw [hId, map_id]
    exact h4 i (fun hi => h (Or.inl hi)) (fun hi => h (Or.inr hi))

/-- The intrinsic Sylow certificate, elementary catalogue and six ambient
normalizer containments imply the full fixed-Sylow radical cover. -/
public theorem radicalCover_of_elementary
    (hSylow : IntrinsicSylow) (hcatalogue : ElementaryCatalogue)
    (hnormalizers : ElementaryNormalizerCover) : Max4RadicalNormalizerCover := by
  obtain ⟨S, hS⟩ := hSylow
  refine ⟨S, ?_⟩
  intro U hU hUS hSU hmax
  rw [hS] at hUS hSU
  obtain ⟨E, hE, hEU, hElem, hNE⟩ :=
    exists_nontrivial_elementary_with_normalizer_le U hU.isPGroup hU.1
  obtain ⟨i, hi⟩ := hcatalogue E hE (hEU.trans hUS) (hSU.trans hNE) hElem
  rw [hi] at hNE
  apply coatom_equiv_candidates_of_le_conjugate _ hmax
  exact (hnormalizers i).imp
    (fun ⟨g, hg⟩ => ⟨g, hNE.trans hg⟩)
    (fun ⟨g, hg⟩ => ⟨g, hNE.trans hg⟩)

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
