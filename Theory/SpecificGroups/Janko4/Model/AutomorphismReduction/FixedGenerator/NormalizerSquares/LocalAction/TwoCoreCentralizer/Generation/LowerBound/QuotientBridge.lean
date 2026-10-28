module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientModel
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientBridge.Certificates
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientBridge.Descent

/-!
# The original max2 subgroup acts on the explicit twelve-dimensional quotient

The checked 62-row embedding and coordinate retraction realize an invariant
subspace of the original ATLAS row module. Its first 50 coordinates form an
invariant subspace; projection onto the last 12 coordinates gives exactly
`quotientX` and `quotientY`. The descent construction extends these two
identities to a homomorphism on the literal closure of `w10` and `w14`.

This uses right row multiplication throughout. No comparison with the
left-column homology action, quotient order, or kernel size is assumed.
Source: the unchanged ATLAS `TwoCoreCentralizer/source/J4G1-max2W1` and its
attribution; GLS3 Table 5.3i, printed p.270. The untrusted coordinate witnesses
are `LowerBound/source/canonical_quotient.json`; their required identities
are proved in `QuotientBridge.Certificates`.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
namespace LowerBound

private def quotientCoordinates : QuotientBridge.Coordinates 112 62 12 where
  basis := QuotientBridge.decode 112 QuotientBridge.basisRows
  retract := QuotientBridge.decode 62 QuotientBridge.retractRows
  project := QuotientBridge.decode 12 QuotientBridge.projectRows
  section_ := QuotientBridge.decode 62 QuotientBridge.sectionRows
  basis_retract := QuotientBridge.basis_retract
  section_project := QuotientBridge.section_project

private theorem realizes_w10 : quotientCoordinates.Realizes (toMatrix w10) matrixX :=
  ⟨QuotientBridge.decode 62 QuotientBridge.actionXRows,
    QuotientBridge.basis_actionX, QuotientBridge.actionX_project⟩

private theorem realizes_w14 : quotientCoordinates.Realizes (toMatrix w14) matrixY :=
  ⟨QuotientBridge.decode 62 QuotientBridge.actionYRows,
    QuotientBridge.basis_actionY, QuotientBridge.actionY_project⟩

private theorem realizes_generators :
    ∀ g ∈ ({w10, w14} : Set Model), ∃ q, quotientCoordinates.Realizes (toMatrix g) q := by
  intro g hg
  rcases hg with rfl | rfl
  · exact ⟨matrixX, realizes_w10⟩
  · exact ⟨matrixY, realizes_w14⟩

/-- The certified row-subquotient action of the original ATLAS word subgroup. -/
def quotientMap : sourceSubgroup →* QuotientMatrixˣ :=
  (quotientCoordinates.hom toMatrix {w10, w14} realizes_generators).toHomUnits

@[simp] theorem quotientMap_sourceX : quotientMap sourceX = quotientX := by
  apply Units.ext
  exact quotientCoordinates.hom_eq toMatrix {w10, w14} realizes_generators
    sourceX matrixX realizes_w10

@[simp] theorem quotientMap_sourceY : quotientMap sourceY = quotientY := by
  apply Units.ext
  exact quotientCoordinates.hom_eq toMatrix {w10, w14} realizes_generators
    sourceY matrixY realizes_w14

end LowerBound
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
