module

public import Theory.GroupTheory.Amalgam.AutomorphismTransport
public import Theory.GroupTheory.Amalgam.FiniteAutomorphisms
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ResidualAction

/-!
# Faithful normal-base actions on a concrete marked model

A marked identification of the two-perfect residual conjugates the original
overlap action onto the compatible automorphism group of that model. The
already proved action is faithful, so finite model bounds control the original
overlap. Both inclusion maps are retained in this comparison.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.8),
(3.2), and the extension arguments in (3.7)--(3.8), pp.381 and 386--392.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup Theory.GroupTheory RankTwoAmalgam
variable {G : Type*} [Group G] {F : Bool → Subgroup G}
variable {L D R : Type*} [Group L] [Group D] [Group R]

def modelResidualAction (F : Bool → Subgroup G) {α : RankTwoAmalgam L D R}
    (e : Iso (inclusionAmalgam (residualFamily F false) (residualFamily F true)) α) :
    ↥(F false ⊓ F true) →* Iso α α :=
  (automorphismConjEquiv e).toMonoidHom.comp (residualAmalgamAction F)

theorem CubicTreeAction.modelResidualAction_injective (h : CubicTreeAction F)
    {α : RankTwoAmalgam L D R}
    (e : Iso (inclusionAmalgam (residualFamily F false) (residualFamily F true)) α) :
    Function.Injective (modelResidualAction F e) :=
  (automorphismConjEquiv e).injective.comp h.residualAmalgamAction_injective

theorem CubicTreeAction.overlap_card_le_model_automorphisms (h : CubicTreeAction F)
    [Finite L] [Finite D] [Finite R]
    {α : RankTwoAmalgam L D R}
    (e : Iso (inclusionAmalgam (residualFamily F false) (residualFamily F true)) α) :
    Nat.card (F false ⊓ F true : Subgroup G) ≤ Nat.card (Iso α α) :=
  Nat.card_le_card_of_injective (modelResidualAction F e) (h.modelResidualAction_injective e)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
