module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveMixedDistanceOne
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PairReorientation

/-!
# The marked-five distance-one pair with A₅ first

The faithful mixed pair obtained from the original wreath-five hypothesis
has its D₁₀ or Sz(2) quotient first and its A₅ quotient second. Reverse the
pair to place A₅ at alpha and the actual small-solvable quotient at beta.
The ambient completion, quasithinness, Sylow subgroup, both quotient markings
and full Borel equation are retained, and the reduced critical distance
remains one. The small-solvable endpoint still excludes noncommuting critical
pairs.

This is an orientation adapter for the actual Section 15.2 source data. It
neither identifies D₁₀ with Sz(2) nor supplies a criticality assertion for the
fixed alpha-to-beta base edge.
Source: Aschbacher--Smith 15.2.4--8, printed pp.1106--1110;
DGS, *Groups and Graphs* (1985), Theorem B and 8.6--8.7.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Source ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original wreath-five assumption supplies an A₅-first source pair of
critical distance one, preserving the opposite D₁₀/Sz(2) marking and Borel. -/
theorem ChosenSmallSource.HStar_wreath_five_distance_one_oriented_pair
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    ∃ (A : Type u) (_ : Group A) (_ : Finite A)
      (L : Fin 2 → Subgroup A) (S : Subgroup A),
      IsQuasithin A ∧ HypothesisF11 L S ∧
      S ⊔ borel (L 1) S = S ∧
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* alternatingGroup (Fin 5)) ∧
      (Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5) ∨
        Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
      b (Reduction.reducedFamily L S) = 1 ∧
      let F := Reduction.reducedFamily L S
      ∀ v w : Vertex F, IsCriticalPair F v w → ⁅Z F v,Z F w⁆ = ⊥ := by
  obtain ⟨A,hA,hfin,L,S,hqt,hF,hB,hq,ha,hb⟩ :=
    h.HStar_wreath_five_distance_one_mixed_pair hH he
  let := hA
  let := hfin
  have hL : ![L 0,L 1] = L := by
    funext i
    fin_cases i <;> rfl
  have hFpair : HypothesisF11 ![L 0,L 1] S := by
    rw [hL]
    exact hF
  have hFswap : HypothesisF11 ![L 1,L 0] S := hFpair.swap
  refine ⟨A,hA,hfin,![L 1,L 0],S,hqt,hFswap,hB,ha,hq,?_,?_⟩
  · calc
      b (Reduction.reducedFamily ![L 1,L 0] S) =
          b (Reduction.reducedFamily ![L 0,L 1] S) := Reduction.pair_b_swap _ _ _
      _ = 1 := by rw [hL]; exact hb
  · dsimp only
    intro v w hc
    exact Reduction.reduced_critical_commuting_of_small_solvable hFswap true hq hc

end CFSG.Quasithin.Chapter15.Section02
