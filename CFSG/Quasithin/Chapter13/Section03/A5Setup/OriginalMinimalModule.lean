module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter3.Section02.MinimalModuleSelection
public import CFSG.Quasithin.Chapter10.SourceA5OriginalIrreducibility

/-!
# A minimal original setup at the A₅ normalization input

The literal Hypothesis13.3.1 supplies an original fundamental setup, which
can be reselected to minimize its full-module order without changing G,T,L.
Its exact moved central quotient is semisimple, has no fixed vectors, and
has only four-dimensional irreducible constituents. These are unconditional
inputs to the chosen-setup D.3.6/7/21 assembly; no irreducibility or
cross-component centralization is imposed on an arbitrary original seed.
Source: Aschbacher–Smith,10.1 and13.3.2(2), printed pp.741 and884–885,
with the seed replacement in D.3.21, printed pp.204–207.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

local instance originalMovedElementary
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  Chapter10.source_original_full_moved_elementary D

/-- The actual Chapter13 source input permits the minimal original seed choice. -/
theorem exists_original_minimal_semisimple_setup
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧
      IsSemisimpleRepresentation (Chapter10.originalMovedQuotientAction D e) ∧
      BinaryOffender.fixedSpace (Chapter10.originalMovedQuotientAction D e) ⊤ = ⊥ ∧
      ∀ S : Subrepresentation (Chapter10.originalMovedQuotientAction D e),
        S.toRepresentation.IsIrreducible → Module.finrank (ZMod 2) S.toSubmodule = 4 := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  obtain ⟨E,hE⟩ := D.exists_minimal_fullModule
  exact ⟨E,hE,Chapter10.source_a5_original_quotient_semisimple E e,
    Chapter10.source_a5_original_quotient_fixedSpace_eq_bot E e,
    fun S hi => (Chapter10.source_a5_original_constituent_alternatives E e S hi).1⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
