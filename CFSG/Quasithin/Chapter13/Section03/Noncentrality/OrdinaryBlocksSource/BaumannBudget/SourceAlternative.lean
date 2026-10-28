module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.SixAlternative
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.Assembly

/-!
# Applying the ordinary natural-six block alternative

The original maximal A₆ choice supplies the genuine Hypothesis12.2.1.
The completed A₆/S₆ action split therefore turns escape of the literal
Baumann normalizer into the original alternating-six block. Applying it
removes the block-alternative premise from the original chief budget and
from the diagonal-block and plane-noncentrality consumers.

The diagonal Baumann identity and module sieve remain separate local proof
targets owned by qt-d-13314-ordinary-blocks. The earlier 13.3.2 and 12.2.13
inputs retain their source producers; no claim of full 13.3.14 is made here.
Source: Aschbacher--Smith 13.3.10(2), 13.3.14, printed pp.887,893.
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

/-- The source A₆ block alternative on the original R₁ and component. -/
theorem ordinaryBaumannBlockAlternative_of_original_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    OrdinaryBaumannBlockAlternative d :=
  OrdinarySix.block_of_baumann_escape d eL
    (Chapter14.Section08.LieTypeBranch.hypothesis1221_of_maximal_six hmax eL)

/-- Only the diagonal Baumann identity remains in the chief-budget construction. -/
theorem ordinaryChiefBudgetSource_of_identity
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (identity : OrdinaryBaumannIdentitySource d) : OrdinaryChiefBudgetSource d :=
  ordinaryChiefBudgetSource_of_baumann_steps d hmax eL escape h1332 identity
    (ordinaryBaumannBlockAlternative_of_original_source d hmax eL)

/-- The literal selected-component consumer with the A₆ alternative discharged. -/
theorem ordinaryBlockSource_of_module_and_identity
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (rows : OrdinaryMovedModuleSource d)
    (identity : OrdinaryBaumannIdentitySource d) : OrdinaryBlockSource d :=
  ordinaryBlockSource_of_module_and_baumann_steps d hmax eL escape h1332 rows identity
    (ordinaryBaumannBlockAlternative_of_original_source d hmax eL)

/-- The original plane consumer retains just the still-open local sieve and identity. -/
theorem ordinary_plane_noncentral_of_module_and_identity
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (rows : ⁅H.pCoreIn 2,E⁆ = ⊥ → OrdinaryMovedModuleSource d)
    (identity : ⁅H.pCoreIn 2,E⁆ = ⊥ → OrdinaryBaumannIdentitySource d) :
    ⁅H.pCoreIn 2,E⁆ ≠ ⊥ :=
  ordinary_plane_noncentral_of_module_and_chief_sources d hmax eL h1332 escape rows
    (fun hc => ordinaryChiefBudgetSource_of_identity d hmax eL escape h1332 (identity hc))

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
