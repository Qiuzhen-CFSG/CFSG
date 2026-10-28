module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Block
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The local closure lies in the two-core of its normalizer

The closure `F.U` is a 2-group by the source local setup. Since it is generated
by the conjugates of the seed under `F.H`, it is normalized by `F.H`; the
standard maximality of `O₂(F.H)` therefore gives `F.U ≤ O₂(F.H)`.

This is only one direction of the 14.4.5 equality. The reverse inclusion
requires the source ambient fusion argument and is not asserted here.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original order-32 closure is a normal 2-subgroup of its literal `H`.
This proves the forward inclusion in the source equality `U = O₂(H)`. -/
theorem source_closure_le_twoCore (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    F.U ≤ F.H.pCoreIn 2 := by
  let := chosen.elementary
  have hp : IsPGroup 2 F.U :=
    (source_closure d earlier hq chosen structural alternatives F hne).1
  exact le_pCoreIn_of_normalizes hp F.U_le_H (le_normalizer_conjugateSpanBy V F.H)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
