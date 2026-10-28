module

public import Theory.GroupTheory.Amalgam.NormalBaseAction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ResidualPrimitive

/-!
# The original overlap acting on Goldschmidt's two-perfect residual amalgam

The proved residual reduction supplies generation, the common-overlap
supplement and primitivity. Consequently, the original overlap embeds in the
group of compatible automorphisms of the residual amalgam, with both literal
inclusion maps preserved. This is the source input for comparing normal-base
extensions with the concrete G₂(2) and Mathieu amalgam automorphism groups.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.8),
(3.2) and (3.7)--(3.8), printed pp.381 and 386--392.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}
open RankTwoAmalgam

/-- The original overlap acts on the marked local pair of its true residual. -/
abbrev residualAmalgamAction (F : Bool → Subgroup G) :
    ↥(F false ⊓ F true) →*
      Iso (inclusionAmalgam (residualFamily F false) (residualFamily F true))
        (inclusionAmalgam (residualFamily F false) (residualFamily F true)) :=
  normalOverlapAction (pResidual 2 G) (F false) (F true)

/-- The complete source reduction supplies every hypothesis of faithful action. -/
theorem CubicTreeAction.residualAmalgamAction_injective (h : CubicTreeAction F) :
    Function.Injective (residualAmalgamAction F) :=
  normalOverlapAction_injective _ _ _ h.residual_source.2.2
    h.common_core_eq_bot h.residual_generated

/-- The original F.6 triple gives the faithful normal-base extension action. -/
theorem universalResidualAction_injective_of_goldschmidt [Finite G]
    {A B : Subgroup G} (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥) :
    Function.Injective (residualAmalgamAction (Universal.cosetFamily (inclusionAmalgam A B))) :=
  (universalCubicTreeAction_of_goldschmidt h hcore).residualAmalgamAction_injective

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
