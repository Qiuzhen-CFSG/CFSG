module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ComplementAction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.AbelianConsequences
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.Commutativity
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.NoncyclicOrder

/-!
# The shape of the actual odd centralizer complement

LocalAction and FourAction construct the actual four-group action and prove
its fixed-subgroup factorization and order restrictions. Commutativity uses
ambient involution fusion and the elementary abelian Sylow two-subgroups to
prove that every actual odd complement is abelian. This discharges the
universal commutativity premise in NoncyclicOrder, which restricts noncyclic
complements to order twenty-seven.

AbelianConsequences supplies the cyclic orders and elementary structure in
the order-27 case. The final theorem assembles these results without any
additional commutativity, cardinality or normalizer premise. The separate
exceptional-normalizer construction and exclusion remain with the consumer.

Source: Bender (1974), proof of (4.1), printed p.225, invoking Janko (1966),
proof of Lemma 3.1, DOI 10.1016/0021-8693(66)90010-X.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Conditional assembly of the two remaining ambient-group obligations.
This is not the unconditional shape theorem. -/
public theorem oddCentralizerShape_of_commutative_of_noncyclic_card
    (h : Janko1CentralizerData G) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (A : Subgroup G) (a : OddCentralizerComplement h x A)
    (hcomm : IsMulCommutative A) (hcard : ¬ IsCyclic A → Nat.card A = 27) :
    (IsCyclic A ∧ (Nat.card A = p ∨ Nat.card A = 15)) ∨
      (IsElementaryAbelian 3 A ∧ Nat.card A = 27) := by
  by_cases hc : IsCyclic A
  · exact Or.inl ⟨hc, a.card_eq_prime_or_fifteen_of_cyclic p hp hxC hx hc⟩
  · exact Or.inr ⟨a.elementary_of_commutative_of_card_twenty_seven p hp hxC hx hcomm (hcard hc),
      hcard hc⟩

/-- The actual odd complement is cyclic of order `p` or fifteen, or elementary
abelian of order twenty-seven, under only the source ambient hypotheses. -/
public theorem oddCentralizerShape
    (h : Janko1CentralizerData G) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (A : Subgroup G) (a : OddCentralizerComplement h x A) :
    (IsCyclic A ∧ (Nat.card A = p ∨ Nat.card A = 15)) ∨
      (IsElementaryAbelian 3 A ∧ Nat.card A = 27) := by
  refine oddCentralizerShape_of_commutative_of_noncyclic_card h p hp x hxC hx A a
    (a.isMulCommutative p hp hxC hx) ?_
  exact a.card_eq_twenty_seven_of_noncyclic
    (fun _ q hq _ hyC hy _ b => b.isMulCommutative q hq hyC hy) p hp hxC hx

end CFSG.Quasithin.Janko1CentralizerData
