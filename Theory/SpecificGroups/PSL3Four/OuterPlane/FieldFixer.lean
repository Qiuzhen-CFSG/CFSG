module

public import Theory.SpecificGroups.PSL3.FieldComponentFixer
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!
# The standard pointwise fixer of the binary subgroup in PSL₃(4)

An automorphism in the concrete linear–field–graph subgroup which fixes every
Frobenius-fixed projective matrix is either identity or Frobenius. The roots
over the fixed coefficient field lie in the genuine projective fixed subgroup.
The imported matrix calculation removes projective scalar ambiguity by trace,
forces the linear factor to act trivially, and excludes the graph factor.
Its fixed-field calculation leaves only powers of Frobenius, whose square is
identity.

This concerns the Frobenius-fixed PSL₃(2), not the graph-field residual E₉.
It requires neither arbitrary-automorphism coverage nor lifting to a cover.
Source: Aschbacher–Smith, proof of 15.3.38, printed p.1137 (PDF p.1154),
`refs/quasithin.pdf`; the standard actions are the matrix actions of GLS3,
Theorem 2.5.12 and §2.7, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Subgroup Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Four.OuterPlane.FieldFixer

private theorem fieldAction_frobenius :
    PSL3.OuterSolvable.fieldAction F fieldFrobenius = pslFrobenius := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H A =>
    rw [pslFrobenius_mk, PSL3.OuterSolvable.fieldAction_mk]
    rfl

private theorem fieldRoots_le_fixedSubgroup :
    PSL3.FieldComponentFixer.fieldRoots fieldFrobenius ≤ pslFrobenius.fixedSubgroup := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, j, hij, c, hc, rfl⟩
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  rw [← fieldAction_frobenius, PSL3.FieldComponentFixer.fieldAction_rootElement, hc]

/-- A standard automorphism fixing the genuine Frobenius-fixed binary subgroup
pointwise is identity or Frobenius. -/
theorem standard_fixer_eq_one_or_frobenius (b : MulAut PSL)
    (hb : b ∈ standard F)
    (hfix : ∀ x ∈ pslFrobenius.fixedSubgroup, b x = x) :
    b = 1 ∨ b = pslFrobenius := by
  classical
  have hm : b ∈ standard F ⊓ fixingSubgroup (MulAut PSL)
      (PSL3.FieldComponentFixer.fieldRoots fieldFrobenius : Set PSL) :=
    ⟨hb, fun x => hfix x.val (fieldRoots_le_fixedSubgroup x.property)⟩
  rw [PSL3.FieldComponentFixer.standard_fixer_eq, MonoidHom.map_zpowers,
    fieldAction_frobenius] at hm
  have hf : IsOfFinOrder pslFrobenius :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, pslFrobenius_sq⟩
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (hf.mem_zpowers_iff_mem_range_orderOf.mp hm)
  have hle : orderOf pslFrobenius ≤ 2 :=
    orderOf_le_of_pow_eq_one (by decide) pslFrobenius_sq
  have hn' : n < 2 := (Finset.mem_range.mp hn).trans_le hle
  interval_cases n
  · exact Or.inl (by simpa only [pow_zero] using he.symm)
  · exact Or.inr (by simpa only [pow_one] using he.symm)

end Matrix.PSL3Four.OuterPlane.FieldFixer
