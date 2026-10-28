module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson.Centralizers
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson.Divisibility

/-!
# Exact order of the concrete J₄ matrix group

The full centralizers of the two certified involution representatives have
orders 21799895040 and 1816657920, in ratio twelve. The actual local census
covers the B,B slice by three centralizer conjugacy classes of sizes at most
2772, 221760 and 532224. The refined Thompson formula transfers these orbit
bounds to 231, 18480 and 44352 and bounds the ambient order strictly below
three times the source order.

Independently, the source order divides the ambient order by certified subgroup
and element orders. Its quotient is positive and odd by the actual ambient
two-part. The strict upper bound therefore makes that quotient one. All finite
census, centralizer-generation, fusion and parity premises are discharged for
the original matrix carrier; no simplicity or perfectness is needed.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, A.6.1–4, printed pp.64–65,
with the local-conjugacy refinement in `TwoInvolutionClassLocalBounds`.
ATLAS representation: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ ,
`J4G1-f2r112B0`; source order
`2^21 * 3^3 * 5 * 7 * 11^3 * 23 * 29 * 31 * 37 * 43`.
-/

public section
namespace Janko4.Cardinality.Thompson
open LocalInvolutionCensus
open Theory.GroupTheory.TwoInvolutionClassLocalBounds

/-- The refined local-conjugacy count is strictly below three source orders. -/
theorem model_card_le_thompson :
    Nat.card Model ≤ 1816657920 * 140813665476 := by
  have hratio : Nat.card (Centralizer z) = 12 * Nat.card (Centralizer t) := by
    rw [centralizer_z_card, centralizer_t_card]
  have hsize : ∀ i : Fin 3, ![2772, 221760, 532224] i =
      12 * ![231, 18480, 44352] i := by decide
  have h := card_le_of_local_conjugacy_cover z t orderOf_z orderOf_t not_isConj_z_t
    involution_classes 12 112266 262144 6820 (![231, 18480, 44352])
    (by decide) hratio slice_aa_card_le slice_ba_card_le bbCover bbCover_covers
    (fun i => by simpa only [← hsize i] using bbCover_card_le i) seed_type_card_le
  rw [centralizer_t_card] at h
  norm_num [Fin.sum_univ_succ] at h ⊢
  exact h

/-- The upper bound required to distinguish the positive odd multiple of the source order. -/
theorem model_card_lt_three_source_order :
    Nat.card Model < 3 * 86775571046077562880 :=
  lt_of_le_of_lt model_card_le_thompson (by norm_num)

/-- Exact order of the literal ATLAS matrix carrier, with no additional premises. -/
theorem model_card : Nat.card Model = 86775571046077562880 :=
  model_card_eq_of_thompson_bound model_card_lt_three_source_order

end Janko4.Cardinality.Thompson
