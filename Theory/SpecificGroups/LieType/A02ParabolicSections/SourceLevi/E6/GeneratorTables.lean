module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E6.GeneratorTables.Node5

/-!
# Signed native E6 tables reduced modulo two

The proved integral Geck curves are packed row by row by parity. The general
row-code soundness theorem identifies their reductions with the twelve raw
matrices used by the folded Sp6 certificates. A signed simple pair is checked
in each module to bound the numerical kernel checks.

Source: GLS3 §1.12 and §2.6; Aschbacher–Smith A.2.18, printed p.40.
-/

public section
namespace Theory.SpecificGroups.LieType.SourceLevi.E6.GeneratorTables

/-- All twelve literal signed simple-root curves agree with the packed tables. -/
theorem integer_cast_decode (j : Fin 12) :
    (Operators.Curves.integerGenerator j).map (Int.castRingHom (ZMod 2)) =
      Thompson.BinaryMatrix.decode 78 (RawMatrices.rows j) := by
  fin_cases j
  · exact positive_0
  · exact negative_0
  · exact positive_1
  · exact negative_1
  · exact positive_2
  · exact negative_2
  · exact positive_3
  · exact negative_3
  · exact positive_4
  · exact negative_4
  · exact positive_5
  · exact negative_5

end Theory.SpecificGroups.LieType.SourceLevi.E6.GeneratorTables
