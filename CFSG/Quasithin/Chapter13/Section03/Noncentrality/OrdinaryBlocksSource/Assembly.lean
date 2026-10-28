module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.Contracts
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.SourceEntry
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.Recognition
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryPlaneSource

/-!
# Assembly of the ordinary source block geometry

The module sieve supplies reduction (g) and the action on the literal W_K.
The Baumann argument supplies the two-chief-factor budget on L₁. The source
entry proves W_K nontrivial; the chief calculation and three-subgroups then
identify U(K) with W_K. Intrinsic recognition constructs the actual A₅ block.

The two earlier source targets remain explicit here. This conditional assembly
does not assert original 13.3.14 before their producers are discharged.
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

/-- Construct every literal block conclusion from the independently proved
module sieve and Baumann budget, preserving the actual selected K. -/
theorem ordinaryBlockSource_of_module_and_chief_sources
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (rows : OrdinaryMovedModuleSource d) (chief : OrdinaryChiefBudgetSource d) :
    OrdinaryBlockSource d := by
  intro K hK hKs hm hn hgen hq hU hf
  obtain ⟨hout,hmodel⟩ := rows K hK hKs hm hn hgen hq hU hf
  have hcount := chief K hK hKs hm hn hgen hq hU hf hout hmodel
  obtain ⟨hbound,hlayer⟩ := ordinary_selected_block_layer_of_original_budget d eL hmax escape
    h1332 K hK hq hf hm hn hgen hcount
  have hfaith := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mp hf
  have hblock := ordinary_alternatingBlock_of_moved_model _ _ _
    hfaith.2.1.2.1 hfaith.2.1.2.2 hlayer hmodel
  exact ⟨hblock,hout,hbound⟩

/-- The actual ordinary plane consumer, conditional only on the two remaining
source arguments under the contrary centralization assumption. -/
theorem ordinary_plane_noncentral_of_module_and_chief_sources
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (rows : ⁅H.pCoreIn 2,E⁆ = ⊥ → OrdinaryMovedModuleSource d)
    (chief : ⁅H.pCoreIn 2,E⁆ = ⊥ → OrdinaryChiefBudgetSource d) :
    ⁅H.pCoreIn 2,E⁆ ≠ ⊥ := by
  apply Chapter14.Section08.LieTypeBranch.original_six_plane_noncentral_of_diagonal_source
    d hmax eL h1332 escape
  intro hc
  exact ordinaryDiagonalSource_of_blocks d h1332
    (ordinaryBlockSource_of_module_and_chief_sources d hmax eL h1332 escape (rows hc) (chief hc))

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
