module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14CommonLine243Exclusion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PairedCoreExclusion

/-!
# The paired-core exclusion at the original Chapter14 consumer

The original SourceLocalData produces the actual marked H and M. Their
marked cubic odd cores now have order 3 simultaneously or order 243
simultaneously: the entire order-27-core branch is excluded, including
its last Sylow-729 case. When 27 divides the ambient group order, both
cores therefore have order 243.

This discharges the order-27-core exclusion from the literal Chapter14
inputs. The separate Sylow-nine branch and Atlas G₂(3) equivalence remain
with the recognition owner. SourceLocalData production and final Chapter14
assembly retain their existing owners. Source: Aschbacher–Smith I.4.5,
printed p.417, applied in Theorem14.4.14.
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

theorem source_cubic_paired_core_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      Nat.card (cubicOddCore c t.x)≠27 ∧
      Nat.card (cubicOddCore (swapFactors c) t.y)≠27 ∧
      ((Nat.card (cubicOddCore c t.x)=3 ∧
          Nat.card (cubicOddCore (swapFactors c) t.y)=3) ∨
        (Nat.card (cubicOddCore c t.x)=243 ∧
          Nat.card (cubicOddCore (swapFactors c) t.y)=243)) ∧
      (3^3∣Nat.card G → Nat.card (cubicOddCore c t.x)=243 ∧
        Nat.card (cubicOddCore (swapFactors c) t.y)=243) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  exact ⟨c,t,t.left_oddCore_card_ne_twentySeven,t.right_oddCore_card_ne_twentySeven,
    t.paired_oddCore_final_orders,t.paired_oddCore_maximal_of_cube_dvd⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
