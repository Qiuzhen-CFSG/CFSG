module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14OddCoreGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.OddCoreExclusions

/-!
# The small-core reduction and nonabelian order-27 exclusion in Chapter 14

The original SourceLocalData supplies the literal G2(3) configuration and
marked cubic torus. Its odd cores have order three simultaneously, and
any core of order 27 is elementary abelian and self-centralizing. Thus the
P × Q and nonabelian order-27 steps are discharged at the actual consumer,
without adding simplicity, divisibility, or recognition assumptions.

The remaining Sylow-nine and elementary order-27 exclusions and the
recognition callback remain with `qt-i45-g2-recognition`. The independent
`qt-d-14414-g2-source` task supplies SourceLocalData. Source: Aschbacher–Smith
I.4.5, printed p.417; compare Fong §6C, pp.75–77, for the Sylow-center step.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_cubic_oddCore_exclusions (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      (Nat.card (cubicOddCore c t.x)=3 ↔
        Nat.card (cubicOddCore (swapFactors c) t.y)=3) ∧
      (Nat.card (cubicOddCore c t.x)≠3 →
        Subgroup.centralizer (cubicOddCore c t.x : Set G) =
          (center (cubicOddCore c t.x)).map (cubicOddCore c t.x).subtype) ∧
      (Nat.card (cubicOddCore (swapFactors c) t.y)≠3 →
        Subgroup.centralizer (cubicOddCore (swapFactors c) t.y : Set G) =
          (center (cubicOddCore (swapFactors c) t.y)).map
            (cubicOddCore (swapFactors c) t.y).subtype) ∧
      (Nat.card (cubicOddCore c t.x)=27 →
        IsElementaryAbelian 3 (cubicOddCore c t.x) ∧
          Subgroup.centralizer (cubicOddCore c t.x : Set G) = cubicOddCore c t.x) ∧
      (Nat.card (cubicOddCore (swapFactors c) t.y)=27 →
        IsElementaryAbelian 3 (cubicOddCore (swapFactors c) t.y) ∧
          Subgroup.centralizer (cubicOddCore (swapFactors c) t.y : Set G) =
            cubicOddCore (swapFactors c) t.y) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  exact ⟨c,t,t.oddCore_three_iff,t.left_oddCore_centralizer,t.right_oddCore_centralizer,
    fun h => ⟨t.left_oddCore_twentySeven_elementary h,t.left_oddCore_twentySeven_selfCentralizing h⟩,
    fun h => ⟨t.right_oddCore_twentySeven_elementary h,t.right_oddCore_twentySeven_selfCentralizing h⟩⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
