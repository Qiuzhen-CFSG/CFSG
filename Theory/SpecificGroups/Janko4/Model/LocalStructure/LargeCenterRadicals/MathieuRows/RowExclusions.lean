module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.Octad
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.ResidualQuotients

/-!
# The two actual Mathieu radical rows in the residual exclusions

Conjugation transports the whole normalizer and its full intrinsic two-core.
The native kernel and octad-preimage rows therefore retain their actual M24
and A8 quotients under every ambient conjugation. A normal residual with the
original quotient order 168 or 6048 excludes both families.

Source: An--O'Brien--Wilson (2003), Table 1, p.124. This calculation proves
these rows and their exclusions; exhaustive large-center radical placement
remains a separate assertion.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
open ElementaryNormalizerCover

/-- Conjugation transports the whole normalizer and its intrinsic core together. -/
def conjugateNormalizerQuotientEquiv (P : Subgroup Model) (g : Model) :
    let N := normalizer (P.map (MulAut.conj g).toMonoidHom : Set Model)
    let H := normalizer (P : Set Model)
    N ⧸ pCore 2 N ≃* H ⧸ pCore 2 H :=
  coreQuotientCongr
    (((MulAut.conj g).subgroupMap (normalizer (P : Set Model))).trans
      (MulEquiv.subgroupCongr (map_equiv_normalizer_eq P (MulAut.conj g)))).symm

/-- Every actual conjugate of the kernel row has its full M24 quotient. -/
def conjugateKernelQuotientEquiv (g : Model) :
    let N := normalizer (embeddedKernel.map (MulAut.conj g).toMonoidHom : Set Model)
    N ⧸ pCore 2 N ≃* Sporadic.Mathieu.M24 :=
  (conjugateNormalizerQuotientEquiv embeddedKernel g).trans kernelNormalizerQuotientEquiv

/-- Every actual conjugate of the octad row has its full A8 quotient. -/
def conjugateOctadQuotientEquiv (O : Sporadic.Mathieu.M24LocalGeometry.Octad) (g : Model) :
    let N := normalizer ((octadRadical O).map (MulAut.conj g).toMonoidHom : Set Model)
    N ⧸ pCore 2 N ≃* alternatingGroup (Fin 8) :=
  (conjugateNormalizerQuotientEquiv (octadRadical O) g).trans (octadRadicalQuotientEquiv O)

/-- The original quotient exclusions remove both literal Mathieu radical rows,
including all their ambient conjugates. This does not assert row coverage. -/
theorem not_mathieu_rows_of_quotients_excluded (P : Subgroup Model)
    (h : let N := normalizer (P : Set Model)
      ¬ (Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
         Nonempty ((N ⧸ pCore 2 N) ≃* Sporadic.Mathieu.M24) ∨
         Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 8)))) :
    (∀ g : Model, P ≠ embeddedKernel.map (MulAut.conj g).toMonoidHom) ∧
      ∀ (O : Sporadic.Mathieu.M24LocalGeometry.Octad) (g : Model),
        P ≠ (octadRadical O).map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro g he
    subst P
    exact h (Or.inr (Or.inl ⟨conjugateKernelQuotientEquiv g⟩))
  · intro O g he
    subst P
    exact h (Or.inr (Or.inr ⟨conjugateOctadQuotientEquiv O g⟩))

/-- A whole-normal residual of either source order excludes both actual native rows. -/
theorem normal_residual_not_mathieu_rows (P : Subgroup Model)
    (B : Subgroup (normalizer (P : Set Model))) [B.Normal]
    (hc : Nat.card (B ⧸ pCore 2 B) = 168 ∨ Nat.card (B ⧸ pCore 2 B) = 6048) :
    (∀ g : Model, P ≠ embeddedKernel.map (MulAut.conj g).toMonoidHom) ∧
      ∀ (O : Sporadic.Mathieu.M24LocalGeometry.Octad) (g : Model),
        P ≠ (octadRadical O).map (MulAut.conj g).toMonoidHom :=
  not_mathieu_rows_of_quotients_excluded P (normal_residual_excludes_three_quotients B hc)

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
