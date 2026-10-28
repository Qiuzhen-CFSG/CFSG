module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Interfaces
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Evaluation.Multiplicity
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Evaluation.Scalars
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Evaluation.Tensor

/-!
# Assembly of common-field tensor evaluation

The diagonal Schur-field actions of the two homogeneous restrictions align
inside the field of endomorphisms of the jointly irreducible action. These
common scalars respect every binary constituent embedding. The actual
Hom-space action then gives bijective tensor evaluation, and its equivariant
identification with the specified right constituent gives the original tensor
output, preserving both binary actions.

`tensorRealization` combines these constructions and discharges both premises
of the retained conditional assembly. Equal Schur-field orders are an input;
neither equal constituent dimensions nor quasiequivalence is required here.

Source: Aschbacher--Smith, combined manuscript, G.9.3, printed p.356,
first paragraph.
-/

public noncomputable section

open scoped TensorProduct
open Representation

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField

universe u v


/-- Final assembly of the unchanged realization contract, conditional on the
two separate mathematical construction theorems. -/
theorem tensorRealization_of_scalars_and_evaluation
    (scalars : CommonScalarTheorem.{u,v})
    (evaluation : TensorEvaluationTheorem.{u,v}) : TensorRealizationTheorem.{u,v} := by
  intro G _ _ V _ _ _ ρ L L₂ C D hc hirr hcard
  obtain ⟨S⟩ := scalars ρ L L₂ C D hc hirr hcard
  obtain ⟨e⟩ := evaluation ρ L L₂ C D S hc hirr
  exact ⟨S.toScalarTensorRealization e⟩

/-- Commuting, jointly irreducible homogeneous actions with equal Schur-field
orders admit compatible common scalars and an equivariant tensor realization
on their specified constituent spaces. -/
theorem tensorRealization : TensorRealizationTheorem.{u,v} :=
  tensorRealization_of_scalars_and_evaluation commonScalars tensorEvaluation

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField
