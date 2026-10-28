module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.Arithmetic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution

/-!
# Fusion and the order calculation for the J₁ local hypotheses

`Janko1CentralizerData.involutions_conjugate` proves fusion from exactly the
original finite simple group hypotheses. `Janko1CentralizerData.card_eq`
constructs the odd-prime data, uses it to obtain the actual coset counts,
and applies the numerical order calculation. Simplicity excludes the other
two candidate orders, leaving 175560 with no additional premises.

Source: Aschbacher–Smith I.4.9, printed p.418; Bender, *Finite groups with
large subgroups* (1974), §4, pp.225–228. This module does not assert recognition
or infer an isomorphism from a group order.
-/

namespace CFSG.Quasithin.Janko1CentralizerData

/-- The order assembly consumes the same parameter in the odd-prime and
coset calculations; both source inputs remain explicit. -/
public theorem card_eq_of_bender_data
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ}
    (localData : BenderPrimeData G d) (counts : BenderCountData G d) :
    Nat.card G = 175560 :=
  h.card_eq_of_bender_counts localData.d_cases counts

/-- Bender's order calculation from the original I.4.9 local hypotheses
and ambient simplicity. The odd-prime and coset-count inputs are both
constructed from these hypotheses. -/
public theorem card_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) : Nat.card G = 175560 := by
  obtain ⟨d, localData⟩ := h.exists_benderPrimeData
  obtain ⟨counts⟩ := h.bender_countData localData
  exact h.card_eq_of_bender_data localData counts

end CFSG.Quasithin.Janko1CentralizerData
