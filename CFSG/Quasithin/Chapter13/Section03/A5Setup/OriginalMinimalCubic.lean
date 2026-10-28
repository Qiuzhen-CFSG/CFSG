module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMinimalModule
public import CFSG.Quasithin.Chapter10.SourceA5NumericalSelection

/-!
# The chosen original Chapter 13 setup has its full cubic bound

Reselect the original fundamental setup without changing G,T,L. The actual
multiple-overgroup branch supplies the outside-maximal witness for this same
setup, and the proved numerical source theorem gives its full cubic bound.
The moved quotient keeps semisimplicity, zero fixed space, and four-dimensional
irreducible constituents. Its irreducibility and support separation are still
the independent module-selection conclusions.

Source: Aschbacher--Smith 3.2.6, 10.1 and13.3.2(2), printed pp.581,741,884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

local instance (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  Chapter10.source_original_full_moved_elementary D

/-- The original source setup in the final multiple-overgroup branch supplies
both the minimal choice and its proved numerical input. -/
theorem exists_original_minimal_cubic_setup
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ Chapter10.SourceFullModuleCubicBound D ∧
      IsSemisimpleRepresentation (Chapter10.originalMovedQuotientAction D e) ∧
      BinaryOffender.fixedSpace (Chapter10.originalMovedQuotientAction D e) ⊤ = ⊥ ∧
      ∀ S : Subrepresentation (Chapter10.originalMovedQuotientAction D e),
        S.toRepresentation.IsIrreducible → Module.finrank (ZMod 2) S.toSubmodule = 4 := by
  obtain ⟨D,hD,hs,hf,hc⟩ := exists_original_minimal_semisimple_setup h e
  exact ⟨D,hD,Chapter10.source_full_module_cubic_bound_of_many D hmany,hs,hf,hc⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
