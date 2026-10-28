module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Density56
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Density132
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Sections
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.SectionCertificates
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Descent

/-!
# The two small binary Higman–Sims models

The polynomial and orbit certificates prove that the literal published pairs
of degrees 56 and 132 generate their full matrix algebras. The certified
exterior-square sections construct actual marked actions on the duals of the
row quotients, so both actions are absolutely irreducible. All numerical
premises are discharged here; only the marked degree-twenty comparison remains
explicit. Its construction and the four-model assembly belong to their
respective producers.

Source: ATLAS HSG1-f2r56B0 and HSG1-f2r132B0. Original matrices, hashes,
source attribution and certificate discovery are in `Binary/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Small

/-- The degree-56 matrix fullness contract, with no carrier-descent premise. -/
theorem matrixAlgebraFull_zero : MatrixAlgebraFull 0 := by
  have ha : aMatrix 0 ∈ Algebra.adjoin (ZMod 2) ({aMatrix 0, bMatrix 0} : Set (Mat 0)) :=
    Algebra.subset_adjoin (by left; rfl)
  have hb : bMatrix 0 ∈ Algebra.adjoin (ZMod 2) ({aMatrix 0, bMatrix 0} : Set (Mat 0)) :=
    Algebra.subset_adjoin (by right; rfl)
  exact D56.algebra_eq_top _ ha hb

/-- The degree-132 matrix fullness contract, with no carrier-descent premise. -/
theorem matrixAlgebraFull_one : MatrixAlgebraFull 1 := by
  have ha : aMatrix 1 ∈ Algebra.adjoin (ZMod 2) ({aMatrix 1, bMatrix 1} : Set (Mat 1)) :=
    Algebra.subset_adjoin (by left; rfl)
  have hb : bMatrix 1 ∈ Algebra.adjoin (ZMod 2) ({aMatrix 1, bMatrix 1} : Set (Mat 1)) :=
    Algebra.subset_adjoin (by right; rfl)
  exact D132.algebra_eq_top _ ha hb

/-- Application to an actual marked degree-56 action. Carrier descent remains explicit. -/
theorem absolutelyIrreducible_zero (C : MarkedAction 0) : C.action.IsAbsolutelyIrreducible :=
  C.absolutelyIrreducible matrixAlgebraFull_zero

/-- Application to an actual marked degree-132 action. Carrier descent remains explicit. -/
theorem absolutelyIrreducible_one (C : MarkedAction 1) : C.action.IsAbsolutelyIrreducible :=
  C.absolutelyIrreducible matrixAlgebraFull_one

/-- The degree-56 marked action, with its numerical section premise discharged. -/
theorem nonempty_markedAction_zero_of_twenty
    (h20 : Nonempty Sporadic.LeechRelated.HS.Twenty.MarkedComparison) :
    Nonempty (MarkedAction 0) :=
  nonempty_markedAction_zero h20 sectionCertificate56

/-- The degree-132 marked action, with its numerical section premise discharged. -/
theorem nonempty_markedAction_one_of_twenty
    (h20 : Nonempty Sporadic.LeechRelated.HS.Twenty.MarkedComparison) :
    Nonempty (MarkedAction 1) :=
  nonempty_markedAction_one h20 sectionCertificate132

/-- The constructed degree-56 action is absolutely irreducible. The only input
is the marked comparison for the degree-twenty carrier action. -/
theorem exists_absolutelyIrreducible_markedAction_zero
    (h20 : Nonempty Sporadic.LeechRelated.HS.Twenty.MarkedComparison) :
    ∃ C : MarkedAction 0, C.action.IsAbsolutelyIrreducible := by
  obtain ⟨C⟩ := nonempty_markedAction_zero_of_twenty h20
  exact ⟨C, C.absolutelyIrreducible matrixAlgebraFull_zero⟩

/-- The constructed degree-132 action is absolutely irreducible. The only input
is the marked comparison for the degree-twenty carrier action. -/
theorem exists_absolutelyIrreducible_markedAction_one
    (h20 : Nonempty Sporadic.LeechRelated.HS.Twenty.MarkedComparison) :
    ∃ C : MarkedAction 1, C.action.IsAbsolutelyIrreducible := by
  obtain ⟨C⟩ := nonempty_markedAction_one_of_twenty h20
  exact ⟨C, C.absolutelyIrreducible matrixAlgebraFull_one⟩

end Representation.HigmanSims.LargeModels.Binary.Small
