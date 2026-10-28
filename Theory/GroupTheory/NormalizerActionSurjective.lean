module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Recognizing a full normalizer action by its index

For a finite subgroup `U`, the normalizer acts as the whole automorphism
group of `U` whenever `|N(U):C(U)| = |Aut(U)|`. The kernel of the
conjugation action is the centralizer inside the normalizer, so the given
index is the image cardinality. Equality of finite cardinalities then
makes the image the whole automorphism group.

This general action-image criterion supplies the full local actions and
conjugacy calculations in Alperin--Brauer--Gorenstein, Chapter II,
Section 1, Proposition 1 (article pp. 10--11). No ambient finiteness or
specific model of `U` is needed; only `U` is assumed finite.
-/

namespace Subgroup

/-- Equality of the automizer index and the automorphism-group order makes
the normalizer's conjugation action surjective. -/
public theorem normalizerMonoidHom_surjective_of_index_eq_card
    {G : Type*} [Group G] (U : Subgroup G) [Finite U]
    (h : (centralizer (U : Set G)).relIndex (normalizer (U : Set G)) = Nat.card (MulAut U)) :
    Function.Surjective U.normalizerMonoidHom := by
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_card_eq
  rw [← Subgroup.index_ker, Subgroup.normalizerMonoidHom_ker]
  exact h

end Subgroup
