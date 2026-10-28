module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.ModelBounds
public import GorensteinWalter.LinearRingEquiv

/-!
# Representative calculations for small-prime cyclic actors

These contracts require actual generating configurations for one inner and
one diagonal outer involution over each of the four prime fields. Fusion
and field transport in `Reduction` extend them to every cyclic actor in
the full automorphism group, retaining conjugators in PSL₂. Neither
contract asserts that its generating configurations have been constructed.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration
open Subgroup GorensteinWalter

/-- One inner involution and four generating conjugates at each prime. -/
def InnerSeeds : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], (p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23) →
    ∃ t : PSL2 (ZMod p), t ≠ 1 ∧ t ^ 2 = 1 ∧
      ∃ c : Fin 4 → PSL2 (ZMod p),
        closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤

/-- One diagonal outer involution and four inner conjugates at each prime. -/
def OuterSeeds : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], (p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23) →
    ∃ t : PGL2 (ZMod p), t ^ 2 = 1 ∧
      t ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range ∧
      ∃ c : Fin 4 → PSL2 (ZMod p),
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range ≤
          closure (Set.range fun i =>
            Matrix.ProjectiveSpecialLinearGroup.toPGL (c i) * t *
              (Matrix.ProjectiveSpecialLinearGroup.toPGL (c i))⁻¹)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration
