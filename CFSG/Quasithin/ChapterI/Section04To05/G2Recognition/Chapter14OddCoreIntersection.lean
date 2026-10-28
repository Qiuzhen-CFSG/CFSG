module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14OddCoreExclusions
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.OddCoreIntersection

/-!
# Equal cubic-core orders at the original Chapter14 consumer

The genuine SourceLocalData constructs the original G2(3) configuration
and marked torus. The two cubic odd cores have equal order. If that order
is 27, both are elementary abelian and their actual intersection has order
three. The fixed-subgroup product retains both original cubic markings.
This discharges the mixed-core exclusion in the exceptional I.4.5 chain,
with no new simplicity, divisibility, or recognition premise.

Source: Aschbacher–Smith I.4.5, printed p.417, used in 14.4.14. The
SourceLocalData producer is qt-d-14414-g2-source. The Sylow-nine and paired
order-27 exclusions and the recognition callback remain in
qt-i45-g2-recognition.
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

theorem source_cubic_oddCore_intersection (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      Nat.card (cubicOddCore c t.x)=Nat.card (cubicOddCore (swapFactors c) t.y) ∧
      (cubicOddCore c t.x ⊓ Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G) =
        zpowers ((t.x:c.H):G) ⊔ (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)) ∧
      (Nat.card (cubicOddCore c t.x)=27 →
        IsElementaryAbelian 3 (cubicOddCore c t.x) ∧
        IsElementaryAbelian 3 (cubicOddCore (swapFactors c) t.y) ∧
        Nat.card (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G)=3) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  refine ⟨c,t,t.oddCore_card_eq,t.left_oddCore_fixed_decomposition,fun h => ?_⟩
  exact ⟨t.left_oddCore_twentySeven_elementary h,
    t.right_oddCore_twentySeven_elementary (t.right_oddCore_twentySeven_of_left h),
    t.oddCore_intersection_card_of_twentySeven h⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
