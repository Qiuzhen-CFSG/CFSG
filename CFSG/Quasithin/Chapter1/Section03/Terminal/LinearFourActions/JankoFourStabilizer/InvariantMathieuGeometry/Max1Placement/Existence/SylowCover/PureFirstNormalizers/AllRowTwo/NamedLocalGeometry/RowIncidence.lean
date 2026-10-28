module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.IncidenceChecks

/-!
# Exact ambient F incidence for the native rows

Every included row mask is a product of checked labels. Every excluded candidate
has a label not commuting with a row element, so it cannot contain that row.
Exhaustiveness at the marked point upgrades these finite checks to the entire
ambient F family. Consequently membership in its canonical intersection is an
exact condition on the listed occurrences, with no occurrence premise supplied.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489, and Proposition 2.2.3,
p.491; the native ATLAS coordinate conventions are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.RowIncidence
open FiniteConfigurations OccurrenceTable
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree
attribute [local irreducible] modelGroup matrixA matrixB
attribute [local instance 2000] Finset.decidableDforallFinset
attribute [local instance 2000] Finset.decidableExistsAndFinset
set_option Elab.async false

/-- Products of the seven actual labels remain in the same F occurrence. -/
theorem combo_mem (i : Fin 330) (c : Fin 128) : nativeWord (combo i c) ∈ wordF (word i) := by
  suffices h : ∀ n, nativeWord (comboStep i c n) ∈ wordF (word i) from h 7
  intro n
  induction n with
  | zero => simpa only [comboStep,nativeWord_zero] using (wordF (word i)).one_mem
  | succ n ih =>
    simp only [comboStep]
    split
    · rw [← nativeWord_mul_fast]
      exact mul_mem ih (occurrence_label_mem i _)
    · exact ih

/-- Exact incidence with the same literal native subgroups used by the census. -/
theorem row_le_occurrence_iff (i : Fin 26) (j : Fin 330) :
    row i ≤ wordF (word j) ↔ j ∈ containing i := by
  constructor
  · intro hle
    by_contra hn
    have he := exclusions i j hn
    let W := wordF (word j)
    let := wordF_elementary (word j)
    have hm : nativeWord (obstruction i j).1 ∈ W :=
      hle ((nativeWord_mem_row_iff i _).mpr he.1)
    have hp : nativeWord (label j (obstruction i j).2) ∈ W := occurrence_label_mem j _
    exact nativeWord_noncommute _ _ he.2
      (congrArg (fun x : W => (x : Model)) (mul_comm (⟨_,hm⟩ : W) (⟨_,hp⟩ : W)))
  · intro hj
    apply (closure_le _).mpr
    rintro _ ⟨m,hm,rfl⟩
    rw [← positive i j hj m hm]
    exact combo_mem j _

/-- The finite incidence statement describes every ambient F occurrence. -/
theorem mem_row_fOccurrences_iff (i : Fin 26) (Y : Subgroup Model) :
    Y ∈ fOccurrences (row i) ↔ ∃ j ∈ containing i, Y = wordF (word j) := by
  constructor
  · rintro ⟨g,he,hrow⟩
    have hpoint : Y ∈ fOccurrences (zpowers markedT) :=
      ⟨g,he,(zpowers_le.mpr (markedT_mem_row i)).trans hrow⟩
    obtain ⟨j,rfl⟩ := (mem_marked_point_fOccurrences_iff Y).mp hpoint
    exact ⟨j,(row_le_occurrence_iff i j).mp hrow,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨_,wordF_eq _,(row_le_occurrence_iff i j).mpr hj⟩

/-- Membership in the canonical ambient intersection is an exact finite condition. -/
theorem mem_row_fIntersection_iff (i : Fin 26) (x : Model) :
    x ∈ fIntersection (row i) ↔ ∀ j ∈ containing i, x ∈ wordF (word j) := by
  simp only [fIntersection,Subgroup.mem_sInf]
  constructor
  · intro hx j hj
    exact hx _ ((mem_row_fOccurrences_iff i _).mpr ⟨j,hj,rfl⟩)
  · intro hx Y hY
    obtain ⟨j,hj,rfl⟩ := (mem_row_fOccurrences_iff i Y).mp hY
    exact hx j hj

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.RowIncidence
