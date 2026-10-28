module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.BorelMarks.Linear
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.BorelMarks.Five
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
/-!
# Complete typed Borel marks for the original C.1.29 family

Apply the proved linear, A₃, and A₅ constructions to each original chi-zero
block. The complete known-simple ordered-product theorem supplies at most
two such blocks outside the controlled subgroup, with their original
Thompson movement. The resulting family has the full literal Borel marks
needed in E.6.7, while preserving the same blocks and ordered product.

Source: Aschbacher–Smith C.1.29, printed p.134, and E.6.7, p.246.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterE.Section06
open ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Every original moved chi-zero block outside the controlled subgroup has
its literal typed Borel marking. -/
theorem chiZero_block_borel_of_control
    (hf : generalizedFitting G = pCore 2 G) (S : Sylow 2 G) (N L : Subgroup G)
    (hcontrol : (S : Subgroup G).characteristicNormalizerClosure ≤ N)
    (hL : IsChiZeroBlockIn L) (hout : ¬L ≤ N)
    (hmove : L = ⁅L,elementaryAbelianMaxJ (S : Subgroup G)⁆) :
    ChiZeroBlockBorel L (N.subgroupOf L) := by
  rcases hL.2 with ⟨n,hn⟩ | hthree | hfive
  · exact Or.inl ⟨n,hn,linear_block_borel_of_control S N L hcontrol hL.1 hout hmove hn⟩
  · exact Or.inr (Or.inl ⟨hthree,alternating_three_block_borel_of_control
      S N L hcontrol hL.1 hout hthree⟩)
  · exact Or.inr (Or.inr ⟨hfive,alternating_five_block_borel_of_control
      hf S N L hcontrol hL.1 hout hfive⟩)

/-- C.1.29 with its omitted Borel clause restored: the same at-most-two
original blocks retain their movement and literal ordered product. -/
theorem ordered_chiZero_product_borel_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : generalizedFitting G = pCore 2 G) (S : Sylow 2 G) (N : Subgroup G)
    (hcontrol : (S : Subgroup G).characteristicNormalizerClosure ≤ N) :
    ∃ r : ℕ, r ≤ 2 ∧ ∃ L : Fin r → Subgroup G,
      (∀ i, IsChiZeroBlockIn (L i)) ∧ (∀ i, ¬L i ≤ N) ∧
      (∀ i, L i = ⁅L i,elementaryAbelianMaxJ (S : Subgroup G)⁆) ∧
      (∀ i, ChiZeroBlockBorel (L i) (N.subgroupOf (L i))) ∧
      ∀ g : G, ∃ m : N, ∃ b : ∀ i, L i,
        g = (m : G) * (List.ofFn (fun i => (b i : G))).prod := by
  obtain ⟨r,hr,L,hL,hout,hmove,hprod⟩ :=
    ChapterC.RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple
      hG hf S N hcontrol
  exact ⟨r,hr,L,hL,hout,hmove,
    fun i => chiZero_block_borel_of_control hf S N (L i) hcontrol (hL i) (hout i) (hmove i),hprod⟩

end CFSG.Quasithin.ChapterE.Section06
