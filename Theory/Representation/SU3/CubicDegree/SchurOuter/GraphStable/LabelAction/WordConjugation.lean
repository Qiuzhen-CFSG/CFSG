module

public import Theory.Representation.SU3.BinaryDefiningWords.Conjugation
public import Theory.Representation.SL3.BinaryDefiningFactors.FrobeniusPeriod.Coefficients

/-!
# Characters of concrete tensor words under semilinear matrix conjugation

The actual word intertwiner for matrix conjugation removes its linear part.
Functoriality of all four factor actions then moves the remaining entrywise
field map to the coefficient embedding. The application in the unitary graph
argument retains the original special-unitary inclusion and Hermitian form.

Source: GM04, Proposition 4.11, internal pp.31--32.
-/

public section
open scoped MatrixGroups
open Matrix Representation.SL3.BinaryDefiningFactors
namespace Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction
variable {F K G : Type*} [Field F] [Field K] [IsAlgClosed K] [CharP K 2] [Group G]

/-- A semilinear matrix formula acts on the word character by changing its
coefficient embedding by the same field map. -/
theorem word_character_semilinear (ι : F →+* K) (w : List Factor)
    (α β : G →* SL(3,F)) (c : F →+* F) (D : GL (Fin 3) F)
    (hD : ∀ g, D * SpecialLinearGroup.toGL (SpecialLinearGroup.map c (α g)) =
      SpecialLinearGroup.toGL (β g) * D) (g : G) :
    (wordRep ι w).character (β g) = (wordRep (ι.comp c) w).character (α g) := by
  obtain ⟨e⟩ := wordEquiv_of_matrix_conjugacy ι w β
    ((SpecialLinearGroup.map c).comp α) D hD
  have he := congrFun (Representation.char_iso e) g
  change LinearMap.trace K (WordSpace K w) (wordRep ι w (SpecialLinearGroup.map c (α g))) =
    (wordRep ι w).character (β g) at he
  rw [wordRep_map] at he
  exact he.symm

end Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction
