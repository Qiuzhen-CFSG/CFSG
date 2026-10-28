module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14PlaneFusion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.OddCoreGeometry

/-!
# The actual cubic odd-core geometry in the dimension-four source branch

The source configuration supplies two cubic odd cores of exponent three.
The quotient of the first by its original cubic line is elementary abelian,
and the opposite original SL₂(3) factor acts faithfully whenever the core
is larger than that line. The order-27 alternatives retain the actual
central line. Applying the same results to `t.swap` gives the other factor.

This discharges the odd-core exponent and faithful quotient-action steps
of the exceptional q=3 argument from the explicit SourceLocalData. It does
not discharge the Sylow-nine or order-27 exclusions, or the recognize
callback in `recognition_of_source_local`. Those remain in this recognition
task; `qt-d-14414-g2-source` produces the source-local data.
Source: Aschbacher–Smith I.4(G1)–(G2), printed p.417, and Fong–Wong,
Nagoya Math. J.36 (1969), §3B(iii), p.156, §4D, pp.164–165.
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

theorem source_cubic_oddCore_geometry (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      Monoid.exponent (cubicOddCore c t.x) = 3 ∧
      Monoid.exponent (cubicOddCore (swapFactors c) t.y) = 3 ∧
      IsElementaryAbelian 3 (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ∧
      Nat.card (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) * 3 =
        Nat.card (cubicOddCore c t.x) ∧
      (∀ a : cubicOddCore c t.x,
        cubicOppositeQuotientAction c t.x ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩
          (QuotientGroup.mk' (cubicCoreLine c t.x) a) =
            (QuotientGroup.mk' (cubicCoreLine c t.x) a)⁻¹) ∧
      (Nat.card (cubicOddCore c t.x) ≠ 3 →
        Function.Injective (cubicOppositeQuotientAction c t.x)) ∧
      (Nat.card (cubicOddCore c t.x) = 27 →
        IsElementaryAbelian 3 (cubicOddCore c t.x) ∨
          (IsExtraspecial 3 (cubicOddCore c t.x) ∧
            (center (cubicOddCore c t.x)).map (cubicOddCore c t.x).subtype =
              zpowers ((t.x:c.H):G))) ∧
      (Nat.card (cubicOddCore (swapFactors c) t.y) = 27 →
        IsElementaryAbelian 3 (cubicOddCore (swapFactors c) t.y) ∨
          (IsExtraspecial 3 (cubicOddCore (swapFactors c) t.y) ∧
            (center (cubicOddCore (swapFactors c) t.y)).map
              (cubicOddCore (swapFactors c) t.y).subtype = zpowers ((t.y:c.H):G))) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  exact ⟨c, t, t.left_oddCore_exponent, t.right_oddCore_exponent,
    t.left_oddCore_quotient_elementary, t.left_oddCore_quotient_card,
    t.left_oddCore_quotient_inverted, t.left_oddCore_quotient_action_faithful,
    t.left_oddCore_twentySeven, t.right_oddCore_twentySeven⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
