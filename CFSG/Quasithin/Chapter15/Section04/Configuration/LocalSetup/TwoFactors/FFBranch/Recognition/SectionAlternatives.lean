module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.NativeSections
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Exhaustive

/-!
# Module contracts for the last mixed FF exclusions

The ordinary alternatives are actual models of the classifier's moved
submodule or its central quotient. `NativeSections` excludes both on the
literal offender action using the seed centralizer. The two remaining
geometries retain their actual marked G₂ representation or F₄-linear
triple-six action, together with faithfulness of the section.

These definitions are targets for extracting the source module alternatives;
no exhaustive module theorem is assumed or asserted. The conditional
consumer removes the ordinary alternatives by the proved model calculations.
It leaves the exceptional geometries explicit for their independent owners.
The recognition owner must supply that extraction and exclude both geometries
before concluding the S₃ × S₃ quotient identification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.2/B.5.1/B.5.6, pp.86,99–110; K.1.3, p.453; 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open ClassificationComparison ClassificationComparison.FFAlternatives NativeSections
universe u v

/-- The two remaining concrete section geometries. The triple-six plane
convention is the corrected projective-line contract, not the legacy one. -/
inductive ExceptionalSection {D : Type u} [Group D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {L : Subgroup D}
    (s : MovedSection ρ L) : Prop
  | binaryG2 (faithful : Function.Injective s.action)
      (action : MarkedActionEquiv s.action (offenderSubgroup s.action) L
        (g2Natural (ZMod 2)) (commutator (Atlas.G2.Model (ZMod 2))))
  | tripleSix (faithful : Function.Injective s.action)
      (action : FFAlternatives.ProjectiveLine.TripleSixAction s.action L)

/-- A module-comparison target. Each disjunct is actual source action data;
none includes a Sylow-fixed-space conclusion or a quotient identification. -/
def SectionAlternatives {D : Type u} [Group D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {L : Subgroup D}
    (s : MovedSection ρ L) : Prop :=
  SectionModel (s.action.comp L.subtype) ∨
    SectionModel (s.space.toRepresentation.comp L.subtype) ∨ ExceptionalSection s

variable {H : Type u} [Group H] [Finite H]
  (P : Sylow 2 H) (Z : Subgroup H) [IsElementaryAbelian 2 (moduleClosure Z)]
  (hC : centralizer (Z : Set H) = (P : Subgroup H))

/-- Eliminate both ordinary models on the original offender action.
The input disjunction must still be proved from the full source classifier. -/
theorem offenderAction_exceptionalSection_of_models
    (L : Subgroup (offenderGroup P Z hC)) (s : MovedSection (offenderAction P Z hC) L)
    (h : SectionAlternatives s) : ExceptionalSection s := by
  rcases h with h | h | h
  · exact (offenderAction_not_sectionModel P Z hC L s h).elim
  · exact (offenderAction_not_movedSpaceModel P Z hC L s h).elim
  · exact h

/-- The application to the exact section stored by the exhaustive comparison,
without replacing its actor, quotient map, or representation. -/
theorem comparedBranch_exceptionalSection_of_models
    (b : QuasisimpleComparison.ComparedBranch (quotientAction P Z hC))
    (h : SectionAlternatives b.source.sectionData) :
    ExceptionalSection b.source.sectionData :=
  offenderAction_exceptionalSection_of_models P Z hC _ b.source.sectionData h

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
