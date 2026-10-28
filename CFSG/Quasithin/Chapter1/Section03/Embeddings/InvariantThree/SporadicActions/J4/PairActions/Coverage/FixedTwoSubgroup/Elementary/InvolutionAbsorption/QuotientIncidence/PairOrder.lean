module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.Geometry

/-!
# The order of an elementary pair product in the max2 quotient

The checked matrix quotient has order 2661120, so a Sylow two-subgroup
has order 256. An elementary subgroup of order nine intersects it trivially.
When these two subgroups permute setwise, their join therefore has order
2304. This gives an optional reduction of incidence to the conjugacy
classification of subgroups of that order in the concrete matrix group.
The classification remains a separate proof obligation.

Source context: Aschbacher–Smith, Proposition 1.3.4, printed p.511 of
`refs/quasithin.pdf`, citing Aschbacher, *Overgroups of Sylow subgroups in
sporadic groups* (1986). The exact quotient-order certificates are supplied
by the imported `MatrixQuotient` development.
-/

public section
open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- Sylow two-subgroups of the actual matrix quotient have order 256. -/
theorem involutionMatrixSylow_card (S : Sylow 2 LowerBound.quotientSubgroup) :
    Nat.card S = 256 := by
  have hfac : Nat.factorization 2661120 2 = 8 := by decide +kernel
  rw [S.card_eq_multiplicity, involutionMatrixQuotient_card, hfac]
  rfl

/-- Setwise permutability, without normalization, gives pair-product order 2304. -/
theorem involutionMatrixPair_card (S : Sylow 2 LowerBound.quotientSubgroup)
    (R : Subgroup LowerBound.quotientSubgroup) (hE : IsElementaryAbelian 3 R)
    (hR : Nat.card R = 3 ^ 2)
    (hp : (R : Set LowerBound.quotientSubgroup) * (S : Set LowerBound.quotientSubgroup) =
      (S : Set LowerBound.quotientSubgroup) * (R : Set LowerBound.quotientSubgroup)) :
    Nat.card (R ⊔ S.toSubgroup : Subgroup LowerBound.quotientSubgroup) = 2304 := by
  let _ := hE
  have hd : Disjoint R S.toSubgroup :=
    (IsElementaryAbelian.isPGroup 3 R).disjoint_of_coprime S.isPGroup' (by decide)
  have hc := card_set_mul_mul_card_inf R S.toSubgroup
  rw [hd.eq_bot, card_bot, mul_one, ← coe_sup_of_set_mul_comm R S.toSubgroup hp,
    hR, involutionMatrixSylow_card S] at hc
  exact hc

/-- A conjugacy classification of order-2304 subgroups suffices for incidence.
This helper does not assert the classification. -/
theorem elementaryMatrixIncidence_of_order2304
    (hcover : ∀ K : Subgroup LowerBound.quotientSubgroup, Nat.card K = 2304 →
      ∃ (i : Bool) (u : LowerBound.quotientSubgroup),
        K ≤ (involutionMatrixCandidate i).map (MulAut.conj u).toMonoidHom) :
    ElementaryMatrixIncidence := by
  intro S R hE hR hp
  exact hcover _ (involutionMatrixPair_card S R hE hR hp)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
