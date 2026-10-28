module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.CandidateCoverage.WordGeneration
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.CandidateCoverage.Data
public import Theory.GroupTheory.BinaryCollection

/-!
# Normal forms from the J₄ word relations

The square and inverse-conjugacy masks are supported on strictly later
positions. If their evaluations are correct in the actual two-subgroup,
`BinaryCollection.cover_ofFn` expresses every element in ascending binary
form. Generation and the independently certified order 2²¹ then make the
2²¹ forms distinct. Neither consistency nor uniqueness is assumed.

The finite support checks and this implication are proved here. The
231 concrete matrix identities in `CollectionRelations` remain to be
certified; the changed-basis GAP matrices are not used as equalities.

Source: `Theory.GroupTheory.BinaryCollection`, the words in `Candidates.Words`,
and the local order proof in `OddIndex.SylowCandidate`. The raw relations
are retained in `CandidateCoverage/source/census.json`.
-/

@[expose] public section
set_option maxRecDepth 10000
open Subgroup Janko4.OuterReduction.OddIndex
open Theory.GroupTheory.BinaryCollection
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ActionImageCandidates.Coverage

/-- The exact square and inverse-conjugacy identities, in the actual carrier. -/
def CollectionRelations : Prop :=
  (∀ i : Fin 21, generator i * generator i = ActionImageCandidates.product (squareMask i)) ∧
  (∀ i j : Fin 21, i < j →
    (generator i)⁻¹ * generator j * generator i = ActionImageCandidates.product (conjugateMask i j))

/-- Read the selected positions in the existing increasing-bit-order convention. -/
def wordIndices (m : ℕ) : List (Fin 21) :=
  (List.finRange 21).filter (fun i => m.testBit i.val)

/-- All right-hand-side supports are later than the conjugating position. -/
theorem triangular_of_relations (h : CollectionRelations) :
    triangular (List.ofFn generator) := by
  have step (a : Fin 21) (l : List (Fin 21))
      (hlt : ∀ b ∈ l, a < b)
      (hs : ∀ i ∈ wordIndices (squareMask a), i ∈ l)
      (hc : ∀ b ∈ l, ∀ i ∈ wordIndices (conjugateMask a b), i ∈ l)
      (ht : triangular (l.map generator)) : triangular ((a :: l).map generator) :=
    triangular_cons_of_words generator a l (wordIndices (squareMask a))
      (fun b => wordIndices (conjugateMask a b))
      (h.1 a) (fun b hb => h.2 a b (hlt b hb)) hs hc ht
  change triangular (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] : List (Fin 21)).map generator)
  refine step 0 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 1 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 2 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 3 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 4 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 5 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 6 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 7 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 8 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 9 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 10 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 11 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 12 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 13 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 14 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 15 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 16 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 17 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 18 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 19 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine step 20 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  trivial

private theorem product_eq_list (m : ℕ) :
    ActionImageCandidates.product m =
      (List.ofFn (fun i : Fin 21 => generator i ^ (m / 2 ^ i.val % 2))).prod := by
  have he (l : List (Fin 21)) :
      ((l.filter (fun i => m.testBit i.val)).map generator).prod =
        (l.map (fun i => generator i ^ (m / 2 ^ i.val % 2))).prod := by
    induction l with
    | nil => simp
    | cons i l ih =>
      have hb : m / 2 ^ i.val % 2 = 0 ∨ m / 2 ^ i.val % 2 = 1 := by omega
      rcases hb with hb | hb
      · have hbit : m.testBit i.val = false := by
          simp [Nat.testBit_eq_decide_div_mod_eq, hb]
        simp [hbit, hb, ih]
      · have hbit : m.testBit i.val = true := by
          simp [Nat.testBit_eq_decide_div_mod_eq, hb]
        simp [hbit, hb, ih]
  simpa only [ActionImageCandidates.product, List.ofFn_eq_map] using he (List.finRange 21)

/-- Concrete relations plus the known order give unique binary coordinates. -/
theorem product_bijective_of_relations (h : CollectionRelations) :
    Function.Bijective (fun m : Fin (2 ^ 21) => ActionImageCandidates.product m.val) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro x
    obtain ⟨m, hm⟩ := cover_ofFn generator (triangular_of_relations h) x
      (closure_generator.symm ▸ Subgroup.mem_top x)
    exact ⟨m, (product_eq_list m.val).trans hm⟩
  · rw [Nat.card_fin, twoSubgroup_card]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ActionImageCandidates.Coverage
