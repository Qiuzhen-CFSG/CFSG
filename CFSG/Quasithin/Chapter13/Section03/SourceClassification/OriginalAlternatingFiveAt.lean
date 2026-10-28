module

public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.MaximalReduction
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.EarlierModules
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.CentralQuotientFive
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement.Models

/-!
# The guarded original A₅-module producer

The original 13.3.2(3) clause is a statement about every literal chosen
module over every faithful component at one fixed `G,T`.  The component
catalogue supplies the `Hypothesis 12.2.3` premise for that same component;
the remaining source input is the equivariant natural marking of the literal
central quotient of the chosen module.  `ChosenModule.a5_model_of_central_quotient`
then lifts this marking to the original module, preserving the original
quotient map and ambient conjugation action.

This is deliberately a guarded adapter.  It does not turn a bare
`Hypothesis1331` into a module classification and does not assert that an
abstract `L/O₂(L) ≃ A₅` is already a marking of a chosen space.

Source: Aschbacher--Smith 12.2.2(3d) and 13.3.2(3), pp.795 and 885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceClassification
open Chapter12.Section02
open Chapter13.Section01
open Chapter14.Section03.FaithfulSource
open Chapter13.Section03.SourceCompletion
open Chapter13.Section03.Noncentrality.SupercriticalSource

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Produce the exact original A₅ clause at fixed `G,T` from the source's
equivariant natural marking of each literal chosen central quotient.

The callback is the genuine remaining 12.2.2(3d) input: it must provide an
equivalence for `D.chosenCentralQuotient`, together with equivariance for the
literal `D.chosenCentralAction`.  The maximal-source arguments are used only
to recover `Hypothesis1223` for each original faithful component. -/
theorem originalAlternatingFiveModules1332At_of_central_quotient
    (quasisimple : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I))
    (models : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I))
    (natural : ∀ (K : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K →
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
      ∀ (I : Subgroup G) (D : ChosenModule T K I),
        ∃ (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
          (a : D.chosenCentralQuotient ≃ₗ[ZMod 2]
            BinaryPermutation.natural (Fin 5)),
          ∀ (k : K) v,
            a (D.chosenCentralAction k v) =
              Chapter6.Source.a5Module
                (e (QuotientGroup.mk' (pCore 2 K) k)) (a v)) :
    OriginalAlternatingFiveModules1332At T L := by
  intro h K hK hfive I D
  obtain ⟨hK1223, _⟩ := faithful_hypothesis1223_of_maximal_models
    h.hypothesis1311 quasisimple models hK
  obtain ⟨e, a, ha⟩ := natural K hK1223 hfive I D
  exact D.a5_model_of_central_quotient e a ha

end CFSG.Quasithin.Chapter13.Section03.SourceClassification
