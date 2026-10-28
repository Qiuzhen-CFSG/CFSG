module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.NormalizerCalculation.Geometry
public import Mathlib.GroupTheory.IndexNormal

/-!
# Reducing the projective unitary normalizer calculation to geometry

An explicit conjugate escaping the socle makes its normalizer proper.
An element t of the normalizer outside the embedded PGU subgroup gives a
second coset. If every other outside element x satisfies x t⁻¹ ∈ PGU,
there are exactly two cosets. Index two then gives relative normality.
Thus no separate normality assumption, ambient simplicity theorem, or
identification by group order is needed in this reduction.

This is conditional assembly. The two geometric inputs are still proof
obligations on the genuine Ree construction; this module does not assert
`unitaryExtensionNormalizers`. In particular, a bound of two cosets alone
does not supply the outside element or prove properness.

Source: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; PGU₃(q):2 is case 7 in the unconditional
list in the proof of Theorem 5 of Himstedt–Nguyen–Tiep, arXiv:0910.4758, p.3.
-/

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup

private theorem normalizer_calculation_of_geometry
    {G : Type*} [Group G] (S H : Subgroup G)
    (hEscape : ∃ g s : G, s ∈ S ∧ g * s * g⁻¹ ∉ S)
    (hOutside : ∃ t : G, t ∈ normalizer (S : Set G) ∧ t ∉ H)
    (hControl : ∀ t ∈ normalizer (S : Set G), t ∉ H →
      ∀ x ∈ normalizer (S : Set G), x ∉ H → x * t⁻¹ ∈ H) :
    normalizer (S : Set G) ≠ ⊤ ∧
      (H.subgroupOf (normalizer (S : Set G))).Normal ∧
      Nat.card (normalizer (S : Set G) ⧸ H.subgroupOf (normalizer (S : Set G))) = 2 := by
  obtain ⟨g, s, hs, hgs⟩ := hEscape
  have hproper : normalizer (S : Set G) ≠ ⊤ := by
    intro htop
    have hg : g ∈ normalizer (S : Set G) := htop.symm ▸ mem_top g
    exact hgs ((mem_normalizer_iff.mp hg s).mp hs)
  obtain ⟨t, ht, htH⟩ := hOutside
  have hindex : (H.subgroupOf (normalizer (S : Set G))).index = 2 := by
    apply index_eq_two_iff_exists_notMem_and.mpr
    refine ⟨⟨t⁻¹, (normalizer (S : Set G)).inv_mem ht⟩, ?_, ?_⟩
    · change t⁻¹ ∉ H
      simpa only [H.inv_mem_iff] using htH
    · intro x
      by_cases hx : (x : G) ∈ H
      · exact Or.inr hx
      · exact Or.inl (hControl t ht htH x x.property hx)
  exact ⟨hproper, normal_of_index_eq_two hindex, hindex⟩

/-- Assemble the exact normalizer contract from displacement, an outside
element and control of the outside coset. Both geometric obligations must
be discharged before obtaining the unconditional source result. -/
public theorem unitaryExtensionNormalizers_of_geometry
    (hWitnesses : UnitaryNormalizerWitnesses)
    (hControl : UnitaryNormalizerCosetControl) : UnitaryExtensionNormalizers := by
  intro m hm M hM hsolv hR S hSn hSs hSa hC F _ _ J hcard hconj e E
  obtain ⟨hEscape, hOutside⟩ :=
    hWitnesses m hm M hM hsolv hR S hSn hSs hSa hC F J hcard hconj e E
  exact normalizer_calculation_of_geometry (S.map M.subtype) E.embedding.range
    hEscape hOutside
    (hControl m hm M hM hsolv hR S hSn hSs hSa hC F J hcard hconj e E)

end ReeF4.MaximalSubgroups.SimpleNormal
