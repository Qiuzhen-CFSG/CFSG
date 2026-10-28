module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.A5Identity
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.SourceAlternative

/-!
# The ordinary diagonal chief budget and its block consumer

The selected A5 module gives the literal diagonal radical and Baumann
identities. Escape of K from M then makes the Baumann normalizer escape.
The original natural-six block alternative and its A4 quotient count give
the two-chief-factor budget. Thus only the moved-module sieve remains in
the diagonal block and plane-noncentrality applications.

Source: Aschbacher--Smith13.3.10(2) and13.3.14, printed pp.887--888,893.
The remaining module sieve and full block assembly belong to
qt-d-13314-ordinary-blocks; the final13.7--13.8 assembly belongs to
qt-d-1378-source. The genuine13.3.2 and12.2.13 inputs retain their earlier
source producers.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)

/-- The actual ordinary chief budget, with both Baumann steps discharged. -/
theorem ordinaryChiefBudgetSource_of_original_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T) : OrdinaryChiefBudgetSource d :=
  ordinaryChiefBudgetSource_of_identity d hmax eL escape h1332
    (ordinaryBaumannIdentitySource_of_original_source d eL h1332)

/-- The selected-component block consumer retains only the module sieve. -/
theorem ordinaryBlockSource_of_moved_module
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (rows : OrdinaryMovedModuleSource d) : OrdinaryBlockSource d :=
  ordinaryBlockSource_of_module_and_identity d hmax eL escape h1332 rows
    (ordinaryBaumannIdentitySource_of_original_source d eL h1332)

/-- The original plane application, conditional on the still-open source sieve. -/
theorem ordinary_plane_noncentral_of_moved_module
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (rows : ⁅H.pCoreIn 2,E⁆ = ⊥ → OrdinaryMovedModuleSource d) :
    ⁅H.pCoreIn 2,E⁆ ≠ ⊥ :=
  ordinary_plane_noncentral_of_module_and_identity d hmax eL escape h1332 rows
    (fun _ => ordinaryBaumannIdentitySource_of_original_source d eL h1332)

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
