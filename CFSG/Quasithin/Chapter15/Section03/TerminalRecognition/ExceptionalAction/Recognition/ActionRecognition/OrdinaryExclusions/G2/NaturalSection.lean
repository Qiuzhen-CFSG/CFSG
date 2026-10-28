module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.Seed

/-!
# The natural-section interface for the terminal G₂ calculation

Specializing the complete source alternatives must produce the actual moved
section for F*(N), place the first local factor in F*(N), and identify the
section action with the full or derived binary G₂ natural action. This
module specifies that output and proves its marked fixed-space lower bound.

It does not construct the natural section or supply the model upper bound.
Those two independent proofs remain necessary for the G₂ exclusion.
Nonsplit central extensions and ambient fixed summands are retained: only
the marked seed is passed injectively to the central quotient.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.5.1
and B.5.6, printed pp.99 and 105, and the final proof of 15.3.1, p.1155.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

open Theory.GroupTheory

/-- Output required from specialization of B.5.1/B.5.6 in the G₂ branch.
The moved space and central kernel are the actual ones for F*(N), and the
natural action is identified by an intertwiner with its own actor map.
Existence is not asserted here. -/
structure NaturalSection where
  sectionData : MovedSection d.offenderAction (generalizedFitting d.offenderGroup)
  first_le : firstInOffender d ≤ generalizedFitting d.offenderGroup
  natural : Nonempty (ActionEquiv sectionData.action (g2Natural (ZMod 2))) ∨
    Nonempty (ActionEquiv sectionData.action (g2DerivedNatural (ZMod 2)))

/-- The source commutator identity puts the actual seed in this moved section. -/
theorem NaturalSection.seed_le (c : NaturalSection d) :
    planeSubspace V V ≤ c.sectionData.space.toSubmodule := by
  rw [c.sectionData.space_eq]
  exact seed_le_moved d _ c.first_le

omit [Finite H] in
/-- The genuine central kernel is fixed by the first local factor. -/
theorem NaturalSection.central_fixed (c : NaturalSection d) :
    c.sectionData.central.toSubmodule ≤
      fixedSpace c.sectionData.space.toRepresentation (firstInOffender d) := by
  rw [c.sectionData.central_eq]
  intro v hv a
  exact hv ⟨a, c.first_le a.property⟩

/-- The marked fixed-space lower bound holds on the central quotient itself. -/
theorem NaturalSection.firstCore_fixed_finrank_ge_four (c : NaturalSection d) :
    4 ≤ Module.finrank (ZMod 2)
      (fixedSpace c.sectionData.action d.firstCoreInOffender) :=
  section_firstCore_fixed_finrank_ge_four d c.sectionData.space c.sectionData.central
    (c.seed_le d) (c.central_fixed d)

/-- Every intertwining identification transports the lower bound on the same
marked core to the model section. -/
theorem NaturalSection.model_firstCore_fixed_finrank_ge_four (c : NaturalSection d)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) (f : ActionEquiv c.sectionData.action σ) :
    4 ≤ Module.finrank (ZMod 2)
      (fixedSpace σ (d.firstCoreInOffender.map f.groupEquiv.toMonoidHom)) := by
  rw [← fixedSpace_map_equivariant c.sectionData.action σ f.groupEquiv.toMonoidHom
    f.linearEquiv f.intertwines, f.linearEquiv.finrank_map_eq]
  exact c.firstCore_fixed_finrank_ge_four d

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2
