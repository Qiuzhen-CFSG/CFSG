module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Products
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic.AlternatingThree
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.GeneralizedFitting.OddNormalObstruction
public import Mathlib.Algebra.Group.Graph

/-!
# An obstruction to the unguarded block-product interface

Let A = A₄ and Q = A/O₂(A), of order three. In A × Q, both A × 1 and
the graph of the quotient map A → Q are normal and isomorphic to the
short group A. Surjectivity gives their literal ordered set product as
all of A × Q. The central subgroup 1 × Q has order three, so F* is not
the two-core; indeed no subgroup has centralizer contained in the two-core.
Taking K to be the whole group also supplies G=KS for every Sylow two-subgroup.

This disproves the requested implications from the published
`IsProductOfBlocks` definition, including the upper bound in the proposed
C.1.11 application. It does not address a central-product interpretation
or a version retaining the upper-core guard from C.1.9.

Source under examination: Aschbacher--Smith, combined manuscript of
1 March 2004, C.1.7 and C.1.9--11, printed pp.123--124.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BlockProductObstruction

private def graphEquiv {L A : Type*} [Group L] [Group A] (f : L →* A) :
    L ≃* f.graph where
  toFun x := ⟨(x, f x), rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := Subtype.ext (Prod.ext rfl x.property)
  map_mul' x y := Subtype.ext (Prod.ext rfl (f.map_mul x y))

private theorem graph_normal {L A : Type*} [Group L] [Group A]
    [IsMulCommutative A] (f : L →* A) : f.graph.Normal := by
  constructor
  intro x hx g
  change f (g.1 * x.1 * g.1⁻¹) = g.2 * x.2 * g.2⁻¹
  rw [map_mul, map_mul, map_inv, mul_comm (f g.1) (f x.1), mul_inv_cancel_right,
    mul_comm g.2 x.2, mul_inv_cancel_right]
  exact hx

private theorem graph_block {L A : Type*} [Group L] [Group A] [Finite L] [Finite A]
    [IsMulCommutative A] (hL : IsShort L) (f : L →* A) : IsBlock f.graph :=
  ⟨inferInstance, RankOne.Solvable.isShort_of_equiv (graphEquiv f) hL,
    (graph_normal f).isSubnormal⟩

private theorem graph_product {L A : Type*} [Group L] [Group A]
    (f : L →* A) (hf : Function.Surjective f) :
    ((1 : L →* A).graph : Set (L × A)) * (f.graph : Set (L × A)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨y, hy⟩ := hf x.2
  refine ⟨(x.1 * y⁻¹, 1), rfl, (y, x.2), hy, ?_⟩
  exact Prod.ext (inv_mul_cancel_right _ _) (one_mul _)

private theorem graph_product_blocks {L A : Type*} [Group L] [Group A]
    [Finite L] [Finite A] [IsMulCommutative A]
    (hL : IsShort L) (f : L →* A) (hf : Function.Surjective f) :
    IsProductOfBlocks (⊤ : Subgroup (L × A)) := by
  refine ⟨[(1 : L →* A).graph, f.graph], ?_, ?_⟩
  · intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · exact graph_block hL 1
    · exact graph_block hL f
  · change ((1 : L →* A).graph : Set (L × A)) * ((f.graph : Set (L × A)) * 1) = Set.univ
    simpa only [mul_one] using graph_product f hf

/-- The actual alternating group on four letters. -/
abbrev A4 := alternatingGroup (Fin 4)
/-- Its actual quotient by the two-core. -/
abbrev Cubic := A4 ⧸ pCore 2 A4
/-- The product A₄ × (A₄/O₂(A₄)). -/
abbrev Model := A4 × Cubic

/-- The quotient factor has order three. -/
theorem cubic_card : Nat.card Cubic = 3 := by
  have hc : Nat.card (pCore 2 A4) = 4 := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)
  have h := card_eq_card_quotient_mul_card_subgroup (pCore 2 A4)
  rw [alternatingGroup.card_of_card_eq_four (by norm_num), hc] at h
  change 12 = Nat.card Cubic * 4 at h
  omega

private instance cubicCyclic : IsCyclic Cubic := isCyclic_of_prime_card cubic_card

/-- A₄ satisfies every clause of the published short-group definition. -/
theorem a4_short : IsShort A4 := by
  have hp : IsPPerfect 2 A4 := by
    change IsPPerfect 2 (alternatingGroup (Fin 4))
    rw [← Equiv.Perm.twoResidual_eq_alternating]
    exact isPPerfect_pResidual 2
  have hc : Nat.card (pCore 2 A4) = 4 := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)
  have he : IsElementaryAbelian 2 (pCore 2 A4) := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour]
    let hk := alternatingGroup.kleinFour_isKleinFour (by norm_num : Nat.card (Fin 4) = 4)
    exact { toIsMulCommutative := hk.isMulCommutative
            exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  exact (RankOne.Solvable.MinimalParabolic.alternatingThree_of_elementary_four_core
    hp he hc cubic_card).2.1

/-- The whole model is the ordered product of two normal short blocks. -/
theorem product_of_blocks : IsProductOfBlocks (⊤ : Subgroup Model) :=
  graph_product_blocks a4_short (QuotientGroup.mk' (pCore 2 A4))
    (QuotientGroup.mk'_surjective _)

private def cubicFactorEquiv : Cubic ≃* (MonoidHom.fst A4 Cubic).ker where
  toFun a := ⟨(1, a), rfl⟩
  invFun a := a.val.2
  left_inv _ := rfl
  right_inv a := Subtype.ext (Prod.ext a.property.symm rfl)
  map_mul' _ _ := Subtype.ext (Prod.ext (one_mul _).symm rfl)

/-- The central cubic factor obstructs F*(G)=O₂(G). -/
theorem not_fitting : generalizedFitting Model ≠ pCore 2 Model := by
  apply not_characteristicTwo_of_normal_three (MonoidHom.fst A4 Cubic).ker
  exact (Nat.card_congr cubicFactorEquiv.toEquiv).symm.trans cubic_card

/-- The obstruction in the literal subgroup type used by the product contract. -/
theorem not_top_fitting :
    generalizedFitting (⊤ : Subgroup Model) ≠ pCore 2 (⊤ : Subgroup Model) := by
  intro h
  apply not_fitting
  apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 topEquiv).mp
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp h)

/-- The central cubic factor lies in every centralizer and outside the two-core. -/
theorem centralizer_not_le_core (U : Subgroup Model) :
    ¬ centralizer (U : Set Model) ≤ pCore 2 Model := by
  intro h
  let N := (MonoidHom.fst A4 Cubic).ker
  have hc : Nat.card N = 3 :=
    (Nat.card_congr cubicFactorEquiv.toEquiv).symm.trans cubic_card
  have hN : IsPGroup 3 N := IsPGroup.of_card (n := 1) (by simpa using hc)
  have hNC : N ≤ centralizer (U : Set Model) := by
    intro x hx y _
    apply Prod.ext
    · change y.1 * x.1 = x.1 * y.1
      change x.1 = 1 at hx
      simp only [hx, mul_one, one_mul]
    · exact mul_comm _ _
  have hn : N ≤ pCore 3 Model := le_sSup ⟨inferInstance, hN⟩
  have hb : N = ⊥ := le_bot_iff.mp (by
    have hh := le_inf (hNC.trans h) hn
    rwa [(pCore_disjoint_of_ne 2 3 (by decide)).eq_bot] at hh)
  rw [hb, card_bot] at hc
  norm_num at hc

/-- Application of the valid product theorem: the lower containment is strict. -/
theorem core_lt_product_centralizer :
    pCore 2 Model < centralizer ((blockU (⊤ : Subgroup Model)).map
      (⊤ : Subgroup Model).subtype : Set Model) :=
  lt_of_le_not_ge product_of_blocks.core_centralizes_blockU (centralizer_not_le_core _)

/-- The actual Sylow-factorization hypothesis does not repair the upper bound. -/
theorem sylow_factorization_counterexample (S : Sylow 2 Model) :
    IsProductOfBlocks (⊤ : Subgroup Model) ∧
    (∀ g : Model, ∃ k ∈ (⊤ : Subgroup Model), ∃ s ∈ (S : Subgroup Model), k * s = g) ∧
    ¬ centralizer ((blockU (⊤ : Subgroup Model)).map (⊤ : Subgroup Model).subtype :
      Set Model) ≤ pCore 2 Model := by
  refine ⟨product_of_blocks, ?_, centralizer_not_le_core _⟩
  intro g
  exact ⟨g, mem_top _, 1, (S : Subgroup Model).one_mem, mul_one _⟩

end CFSG.Quasithin.ChapterC.BlockProductObstruction
