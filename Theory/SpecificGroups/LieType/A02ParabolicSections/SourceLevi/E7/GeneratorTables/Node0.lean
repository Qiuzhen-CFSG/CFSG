module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E7.Operators.Curves
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E7.RawMatrices
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.BinaryTables

/-!
# Signed native E7 tables reduced modulo two

The proved integral Geck curves are packed row by row by parity. The general
row-code soundness theorem identifies their reductions with the twelve raw
matrices used by the folded Sp6 certificates. A signed simple pair is checked
in each module to bound the numerical kernel checks.

Source: GLS3 §1.12 and §2.6; Aschbacher–Smith A.2.18, printed p.40.
-/

public section
namespace Theory.SpecificGroups.LieType.SourceLevi.E7.GeneratorTables

/-- The literal positive simple-root table at node 0, reduced modulo two. -/
theorem positive_0 :
    (Operators.Curves.integerGenerator 0).map (Int.castRingHom (ZMod 2)) =
      Thompson.BinaryMatrix.decode 133 (RawMatrices.rows 0) := by
  apply BinaryTables.cast_matrix_eq_decode
  decide +kernel

/-- The literal negative simple-root table at node 0, reduced modulo two. -/
theorem negative_0 :
    (Operators.Curves.integerGenerator 1).map (Int.castRingHom (ZMod 2)) =
      Thompson.BinaryMatrix.decode 133 (RawMatrices.rows 1) := by
  apply BinaryTables.cast_matrix_eq_decode
  decide +kernel

end Theory.SpecificGroups.LieType.SourceLevi.E7.GeneratorTables
