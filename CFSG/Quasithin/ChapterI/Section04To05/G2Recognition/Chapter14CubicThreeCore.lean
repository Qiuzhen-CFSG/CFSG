module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14CubicNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicThreeCore

/-!
# Three-core orders in the dimension-four source branch

The original SourceLocalData construct a common torus and two cubic lines
in the original SL₂(3) factors. Their ambient centralizers have odd cores
of order 3, 27, or 243, and these are their actual three-cores. For each
line, either its normalizer lies in H, its odd core has order 27, or 3⁶
divides the ambient group order. No branch-exclusion hypothesis is added.

This applies the cubic odd-core calculation used toward Aschbacher–Smith
I.4.5, p.417, to the source setting of 14.4.3–5, pp.1007–1008. The remaining
prime-three branch exclusions, BN-pair recognition and ambient model
equivalence remain with `qt-i45-g2-recognition`. The consolidated
`qt-d-14414-g2-source` produces SourceLocalData and owns its final discharge.
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

theorem source_cubic_three_core_orders (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      IsPGroup 3 (cubicOddCore c t.x) ∧
      IsPGroup 3 (cubicOddCore (swapFactors c) t.y) ∧
      (Nat.card (cubicOddCore c t.x) = 3 ∨ Nat.card (cubicOddCore c t.x) = 27 ∨
        Nat.card (cubicOddCore c t.x) = 243) ∧
      (Nat.card (cubicOddCore (swapFactors c) t.y) = 3 ∨
        Nat.card (cubicOddCore (swapFactors c) t.y) = 27 ∨
        Nat.card (cubicOddCore (swapFactors c) t.y) = 243) ∧
      pCore 3 (cubicCentralizer c t.x) = pPrimeCore 2 (cubicCentralizer c t.x) ∧
      pCore 3 (cubicCentralizer (swapFactors c) t.y) =
        pPrimeCore 2 (cubicCentralizer (swapFactors c) t.y) ∧
      (cubicNormalizer c t.x ≤ c.H ∨ Nat.card (cubicOddCore c t.x)=27 ∨
        3^6 ∣ Nat.card G) ∧
      (cubicNormalizer (swapFactors c) t.y ≤ c.H ∨
        Nat.card (cubicOddCore (swapFactors c) t.y)=27 ∨ 3^6 ∣ Nat.card G) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  exact ⟨c,t,t.left_oddCore_isThreeGroup,t.right_oddCore_isThreeGroup,
    t.left_oddCore_orders,t.right_oddCore_orders,t.left_threeCore,t.right_threeCore,
    t.left_three_local_alternative,t.right_three_local_alternative⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
