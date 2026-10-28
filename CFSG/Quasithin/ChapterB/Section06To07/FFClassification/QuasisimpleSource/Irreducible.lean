module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.BinaryLinear.Source
/-!
# The original quasisimple source action is Irr+

The actual minimal-parabolic geometry excludes the repeated SL3 row and
all binary higher-linear actors. Applying these exclusions to the original
B.5.1 four-way conclusion leaves its irreducible moved-central-quotient
branch, with the original faithfulness and complete B.4.2 source alternatives.

Source: Aschbacher–Smith B.5.1 and B.6.9, printed pp.99–103 and 116.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction.ProjectiveLine
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
/-- The source B.5.1 section is faithful and irreducible after the genuine actor exclusions. -/
theorem source_offender_quasisimple_irreducible
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    IsIrrPlus (ρ.comp (offenderSubgroup ρ).subtype)
        (generalizedFitting (offenderSubgroup ρ)) c.sectionData.space.toSubmodule ∧
      Function.Injective c.sectionData.action ∧
      IsIrreducible (c.sectionData.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype) ∧
      SourceInduction.ProjectiveLine.IrreducibleActionCase c.sectionData.action (generalizedFitting (offenderSubgroup ρ))
        (offenderSubgroup c.sectionData.action) := by
  have h3 := source_offender_quasisimple_three_exclusions ρ T hP hff hcore hq c
  have hb := source_offender_quasisimple_binary_rows_excluded ρ T hP hff hcore hq c
  cases c.clause_one with
  | irreducible hi hf hir hc he => exact ⟨hi,hf,hir,hc⟩
  | doubleThree F hw e ho hr => exact (h3.2 F 2 (by decide) ⟨e⟩).elim
  | naturalDual d hd hw h => exact (hb.2.2.1 d hd h).elim
  | repeatedNatural d r hd hr hb' hw h => exact (hb.2.1 d r hd h).elim
end CFSG.Quasithin.ChapterB
