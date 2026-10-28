module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.RankTransport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.PairCoverageData

/-!
# All independent-pair ranks in the literal family

The source-conjugacy trees transfer four checked ranks to every independent
pair in every advertised row and to an obstruction pair in each extra pure
sixteen. This checks all pairs, not just pairs from a chosen basis. The actual
native-pair exclusion follows through the established rank criterion.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
open ElementaryNormalizerCover.PureTwoA.NativePair
open PairOrbitData
attribute [local irreducible] modelGroup matrixA matrixB toMatrix row nativeWord pairRank
set_option backward.isDefEq.respectTransparency true
set_option Elab.async false

private theorem goodNode_rank (i : Fin 2707) :
    pairRank (nativeWord (goodNode i).1) (nativeWord (goodNode i).2) = 16 := by
  unfold goodNode
  split
  · exact nodes_rank_0 _
  · split
    · exact nodes_rank_1 _
    · exact nodes_rank_2 _

/-- Every independent pair, including pairs not occurring in a chosen basis. -/
theorem row_pairRank (i : Fin 26) (x y : Model) (hx : x ∈ row i) (hy : y ∈ row i)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) : pairRank x y = 16 := by
  let := row_elementary i
  have hsx := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have hsy := elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy
  have hc : Commute x y :=
    congrArg (fun z : row i => (z : Model)) (mul_comm (⟨x,hx⟩ : row i) ⟨y,hy⟩)
  obtain ⟨m,hm,rfl⟩ := (mem_row_iff i x).mp hx
  obtain ⟨n,hn,rfl⟩ := (mem_row_iff i y).mp hy
  obtain ⟨j,rfl⟩ := rowWords_cover i m hm
  obtain ⟨k,rfl⟩ := rowWords_cover i n hn
  have hj : rowWords i j ≠ 0 := fun h => hx1 (h ▸ nativeWord_zero)
  have hk : rowWords i k ≠ 0 := fun h => hy1 (h ▸ nativeWord_zero)
  have hjk : rowWords i j ≠ rowWords i k :=
    fun h => hxy (congrArg nativeWord h)
  exact (pairRank_sameBasis _ _ hsx hsy hc (row_pair_coverage i j k hj hk hjk)).symm.trans
    (goodNode_rank _)

/-- Every listed row satisfies the actual ambient no-native-pair condition. -/
theorem row_no_native_pair (i : Fin 26) :
    ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ row i := by
  let := row_elementary i
  apply (no_native_pair_iff_pair_rank _ (row_pure i)).mpr
  intro x hx y hy hx1 hy1 hxy
  exact row_pairRank i x y hx hy hx1 hy1 hxy

/-- Each additional pure sixteen has an explicit independent rank-twenty pair. -/
theorem extra_pairRank (i : Fin 5) :
    pairRank (nativeWord (badPair i).1) (nativeWord (badPair i).2) = 20 := by
  let := MarkedIntersection.markedIntersection_elementary
  have hm : ∀ i : Fin 5,
      (∃ j : Fin 128, MarkedIntersection.coordinate j = (badPair i).1) ∧
      (∃ j : Fin 128, MarkedIntersection.coordinate j = (badPair i).2) := by decide +kernel
  obtain ⟨⟨j,hj⟩,⟨k,hk⟩⟩ := hm i
  have h1 : nativeWord (badPair i).1 ∈ MarkedIntersection.markedIntersection :=
    (MarkedIntersection.mem_markedIntersection_iff _).mpr ⟨j,by simpa only [nativeWord] using congrArg nativeWord hj⟩
  have h2 : nativeWord (badPair i).2 ∈ MarkedIntersection.markedIntersection :=
    (MarkedIntersection.mem_markedIntersection_iff _).mpr ⟨k,by simpa only [nativeWord] using congrArg nativeWord hk⟩
  have hc : Commute (nativeWord (badPair i).1) (nativeWord (badPair i).2) :=
    congrArg (fun z : MarkedIntersection.markedIntersection => (z : Model))
      (mul_comm (⟨_,h1⟩ : MarkedIntersection.markedIntersection) ⟨_,h2⟩)
  exact (pairRank_sameBasis _ _ (elemPow_eq_one_of_isElementaryAbelian _ h1)
    (elemPow_eq_one_of_isElementaryAbelian _ h2) hc (bad_pair_coverage i)).symm.trans
      (nodes_rank_3 _)

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
