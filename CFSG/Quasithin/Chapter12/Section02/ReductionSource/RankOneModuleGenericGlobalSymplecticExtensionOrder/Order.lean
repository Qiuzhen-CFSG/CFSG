module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.Completion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.FullNormalizer

/-!
# The prepared symplectic order and classification application in Chapter 12

With W=wholeReduced T L, the original prepared comparison constructs one
full extension and proves equality of its order with the ambient group.
This discharges the existing completion and recognition inputs and gives
the symplectic GlobalExit. The original Hypothesis 12.2.1, many locals,
PSL2 quotient, HStar, Preparation and perfect whole residual are retained.
Both orientations and n=2 are included.

Source: Aschbacher--Smith 5.3.2--4, F.4.31--43 and 12.2.2, printed
pp.658--659,291--296,795 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.SourceCompletion.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F=2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include D h hmany hn hpsl hH d hp hm hF he

/-- The ambient order equals the order of the same coherent full extension. -/
theorem rankOne_global_symplectic_extension_card_eq
    (a : Global.SymplecticNormalizerMarking L (residual H) (Global.sourceS L H) F) :
    Nat.card G=Nat.card a.extension.carrier :=
  d.symplectic_extension_card_eq
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he a

/-- The source inputs construct both the compatible extension and its order bound. -/
theorem rankOne_global_symplectic_extension_order :
    m=n ∧ ∃ E : SourceExtension F,
      (Nonempty (RankTwoAmalgam.Iso (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
       Nonempty (RankTwoAmalgam.Iso (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse)) ∧
      Nat.card G≤Nat.card E.carrier :=
  d.symplectic_extension_order
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- The existing faithful completion with all three extension inputs discharged. -/
theorem rankOne_global_symplectic_prepared_extension_completion :
    let E := (d.symplecticNormalizerMarking
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he).extension
    m = n ∧ Nat.card F = 2^n ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
      ∃ c : Completion E (Global.SymplecticCompletion.join L (residual H)),
        c.middle.range = (normalizer (L : Set G) ⊓ normalizer (residual H : Set G)).subgroupOf
          (Global.SymplecticCompletion.join L (residual H)) ∧
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (Global.SymplecticCompletion.join L (residual H)) ≤ Nat.card E.carrier ∧
        c.middle.range.normalCore = ⊥ ∧
        Function.Injective (MulAction.toPermHom (Global.SymplecticCompletion.join L (residual H))
          (Subgroup.CosetGeometry.RankTwo.Vertex c.cosetFamily)) ∧
        Nat.card c.unipotentMap.range = Nat.card F ^ 4 ∧
        Nat.card c.torusMap.range = (Nat.card F - 1)^2 ∧
        c.torusMap.range ≤ normalizer (c.unipotentMap.range : Set (Global.SymplecticCompletion.join L (residual H))) ∧
        c.unipotentMap.range ⊓ centralizer
          (c.torusMap.range : Set (Global.SymplecticCompletion.join L (residual H))) = ⊥ :=
  d.symplectic_prepared_extension_completion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- The prepared symplectic comparison now yields the original GlobalExit. -/
theorem rankOne_globalExit_of_symplectic_comparison : RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_symplectic_prepared_extension_order h hmany hn hpsl hH d hp F hm hF he
    (d.symplectic_extension_card_eq
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he
      (d.symplecticNormalizerMarking
        (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he)).le

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
