module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveCriticalCommuting
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableCriticalAlternatives

/-!
# The remaining critical branches of the original marked-five pairs

Both the literal marked-five/S₃ pair and the faithful wreath mixed A₅ pair
have original local quotient orders below 72. The small-solvable DGS reduction
therefore excludes all noncommuting pairs and the distance-three branch with
zero displacement. The quotient completion, first factor, common Sylow and
original Borel marking are preserved, including the two-core quotient needed
by the mixed pair.

The remaining distance-one and nonzero distance-three source arguments stay
with the original small-parabolic recognition owner. These reductions do not
supply the global H-star wreath theorem or the independent residual identity.

Source: Aschbacher–Smith 15.2.4–8, printed pp.1106–1110;
DGS, *Groups and Graphs* (1985), Theorem B and 9.10, pp.102,147–150.
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

private theorem small_solvable_quotient_card_lt {A : Type*} [Group A]
    (he : Nonempty (A ≃* DihedralGroup 5) ∨
      Nonempty (A ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) : Nat.card A < 72 := by
  rcases he with he | he
  · rw [Nat.card_congr he.some.toEquiv,DihedralGroup.nat_card]
    norm_num
  · rw [Nat.card_congr he.some.toEquiv,BenderSuzuki.MatrixGroups.suzukiZero_card]
    norm_num

/-- On the original marked-five/S₃ pair, critical distance three has nonzero
displacement; all noncommuting and zero-displacement branches are excluded. -/
theorem ChosenSmallSource.marked_five_symmetricThree_critical_alternatives
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let F := Reduction.reducedFamily ![h.residual ⊔ (M ⊓ Mc).pCoreIn 2,H] (T : Subgroup G)
    ∀ a beta a' : Vertex F, IsCriticalPair F a a' → (graph F).Adj a beta →
      (graph F).dist beta a' + 1 = b F →
      ⁅Z F a,Z F a'⁆ = ⊥ ∧
        (b F = 1 ∨ (b F = 3 ∧ ⁅DGS85.V F beta 1 ⊓ Q F a',DGS85.V F a' 1⁆ ≠ ⊥)) := by
  obtain ⟨hF,hq,_⟩ := h.marked_five_symmetricThree_recognition_data hd hH he
  dsimp only
  intro a beta a' hc hab hdist
  apply Assembly.reduced_small_solvable_critical_alternatives hF false hq ?_ hc hab hdist
  intro i
  fin_cases i
  · exact small_solvable_quotient_card_lt hq
  · change Nat.card (H ⧸ pCore 2 H) < 72
    rw [Nat.card_congr he.some.toEquiv,Nat.card_perm,Nat.card_fin]
    norm_num

/-- The faithful wreath mixed pair has only the distance-one or nonzero
distance-three commuting source branch, on its actual quotient graph. -/
theorem ChosenSmallSource.HStar_wreath_five_critical_alternatives
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
      let F := Reduction.reducedFamily L S
      ∀ a beta a' : Vertex F, IsCriticalPair F a a' → (graph F).Adj a beta →
        (graph F).dist beta a' + 1 = b F →
        ⁅Z F a,Z F a'⁆ = ⊥ ∧
          (b F = 1 ∨ (b F = 3 ∧ ⁅DGS85.V F beta 1 ⊓ Q F a',DGS85.V F a' 1⁆ ≠ ⊥)) := by
  obtain ⟨A,hA,hfin,L,S,hqt,hF,hB,hq,ha,_⟩ := h.HStar_wreath_five_commuting_mixed_pair hH he
  let := hA
  let := hfin
  refine ⟨A,hA,hfin,L,S,hqt,hF,hB,hq,ha,?_⟩
  dsimp only
  intro a beta a' hc hab hdist
  apply Assembly.reduced_small_solvable_critical_alternatives hF false hq ?_ hc hab hdist
  intro i
  fin_cases i
  · exact small_solvable_quotient_card_lt hq
  · change Nat.card (L 1 ⧸ pCore 2 (L 1)) < 72
    rw [Nat.card_congr ha.some.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]

end CFSG.Quasithin.Chapter15.Section02
