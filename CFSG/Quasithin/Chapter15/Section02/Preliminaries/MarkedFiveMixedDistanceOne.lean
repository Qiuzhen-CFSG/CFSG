module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveCriticalAlternatives
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableLinearFourDistance
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# Critical distance one in the original wreath mixed pair

The original wreath-five hypothesis supplies a faithful quasithin completion
with one quotient D₁₀ or Sz(2) and the other A₅. Identify the latter with
PSL₂ over the field of four elements and apply the unequal-parameter DGS
reduction. The completion, original first Borel, common Sylow and both
quotient markings remain in the output; no recognition premise is added.

This removes the distance-three branch. The remaining distance-one source
recognition and global H-star wreath theorem are not asserted here.
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

/-- The original wreath-five assumption produces a faithful mixed pair
whose critical distance is one; the distance-three branch is excluded. -/
theorem ChosenSmallSource.HStar_wreath_five_distance_one_mixed_pair
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    ∃ (A : Type u) (_ : Group A) (_ : Finite A)
      (L : Fin 2 → Subgroup A) (S : Subgroup A),
      IsQuasithin A ∧ HypothesisF11 L S ∧
      S ⊔ borel (L 0) S = S ∧
      (Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
        Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
      Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* alternatingGroup (Fin 5)) ∧
      b (Reduction.reducedFamily L S) = 1 := by
  obtain ⟨A,hA,hfin,L,S,hqt,hF,hB,hq,ha,_⟩ := h.HStar_wreath_five_critical_alternatives hH he
  let := hA
  let := hfin
  refine ⟨A,hA,hfin,L,S,hqt,hF,hB,hq,ha,?_⟩
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  apply Assembly.small_solvable_linear_four_distance_one hF hq ?_ hc (ha.some.trans e₄.symm)
  intro i
  fin_cases i
  · change Nat.card (L 0 ⧸ pCore 2 (L 0)) < 72
    rcases hq with hq | hq
    · rw [Nat.card_congr hq.some.toEquiv,DihedralGroup.nat_card]
      norm_num
    · rw [Nat.card_congr hq.some.toEquiv,BenderSuzuki.MatrixGroups.suzukiZero_card]
      norm_num
  · change Nat.card (L 1 ⧸ pCore 2 (L 1)) < 72
    rw [Nat.card_congr ha.some.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]

end CFSG.Quasithin.Chapter15.Section02
