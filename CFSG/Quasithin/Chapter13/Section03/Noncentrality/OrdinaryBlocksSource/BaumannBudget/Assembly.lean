module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.Inputs
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.Count
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.Projection
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.Assembly

/-!
# Assembly of the original ordinary Baumann budget

The selected-component Baumann identity forces escape from M. The earlier
natural-six alternative gives the original A₆ block, and the actual A₄
quotient calculation bounds every complete chief series of sourceOne.
The block-geometry consumer uses exactly that bound and the independent
module sieve, preserving all original selected-component premises.

The two Baumann source interfaces remain explicit proof obligations; this
conditional assembly does not assert their source theorems.
Source: Aschbacher--Smith, 13.3.14, final paragraph on printed p.893.
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

/-- Exact budget assembly from the two remaining genuine source steps. -/
theorem ordinaryChiefBudgetSource_of_baumann_steps
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (identity : OrdinaryBaumannIdentitySource d)
    (alternative : OrdinaryBaumannBlockAlternative d) : OrdinaryChiefBudgetSource d := by
  intro K hK hKs hm hn hgen hq hU hf hout hmodel s h0 h1
  have he := identity K hK hKs hm hn hgen hq hU hf hout hmodel
  have hescape := ordinary_baumann_escape_of_core_identity d hmax eL escape h1332 K hK hf he
  exact ordinary_chief_count_le_two_of_block d eL (alternative hescape) s h0 h1

/-- The literal block-geometry consumer of the assembled chief budget.
Its module sieve and both earlier Baumann steps retain their own producers. -/
theorem ordinaryBlockSource_of_module_and_baumann_steps
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (rows : OrdinaryMovedModuleSource d)
    (identity : OrdinaryBaumannIdentitySource d)
    (alternative : OrdinaryBaumannBlockAlternative d) : OrdinaryBlockSource d :=
  ordinaryBlockSource_of_module_and_chief_sources d hmax eL h1332 escape rows
    (ordinaryChiefBudgetSource_of_baumann_steps d hmax eL escape h1332 identity alternative)

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
