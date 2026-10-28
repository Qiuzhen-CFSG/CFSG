module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14PairedCoreCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.DiagonalCentralizer

/-!
# The common diagonal centralizer in the original Chapter14 configuration

From the original SourceLocalData, order27 marked odd cores force their
common line to have centralizer of order486 or1458. Its Sylow two-subgroups
have order two, and its actual odd core has index two and order243 or729.
Thus the odd-complement and centralizer-order premises are discharged at
the literal Chapter14 consumer. Excluding these cases and recognizing the
Atlas model remain with the recognition task; the SourceLocalData producer
and final Chapter14 assembly retain their existing owners.

Source: Aschbacher–Smith I.4.5, printed p.417, used in Theorem14.4.14.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_cubic_diagonal_centralizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      Nat.card (cubicOddCore c t.x)=27 →
      let C := Subgroup.centralizer
        ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G)
      (∀ P : Sylow 2 C, Nat.card P=2) ∧
      (pPrimeCore 2 C).index=2 ∧
      (Nat.card (pPrimeCore 2 C)=243 ∨ Nat.card (pPrimeCore 2 C)=729) ∧
      (Nat.card C=486 ∨ Nat.card C=1458) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  refine ⟨c,t,fun h => ?_⟩
  exact ⟨t.core_intersection_sylow_two_card h,(t.core_intersection_oddCore_index h).1,
    t.core_intersection_centralizer_orders h⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
