module

public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.Reduction
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.Centerless.Order
public import Theory.GroupAction.AutomorphismFixedTransport

/-!+# The quartic graph-field fixed-group rank

The whole fixed group of inverse transpose times Frobenius on PSL₃(4) has
order 72 and contains the already constructed quaternion subgroup of order
eight. This subgroup is Sylow, and its square-one elements lie in its center
of order two. Thus the whole fixed group has two-rank at most one.

Transport retains an actual group equivalence and the exact automorphism
identity. The elementary-actor application gives rank at most three when
the outer image has rank at most two. It does not replace the fixed group
by its odd two-residual E₉.

Source: Aschbacher–Smith E.1.14(1), printed p.214; the concrete fixed-group
calculations are those for 16.4.9(2), printed pp.1191–1192.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace Matrix.PSL3Even.OuterElementaryRank

private theorem quaternion_rank : primeRank 2 (QuaternionGroup 2) ≤ 1 := by
  apply primeRank_le_of_pow_eq_one_subset (center (QuaternionGroup 2))
  · rw [Nat.card_eq_fintype_card]
    decide +kernel
  · decide +kernel

open Matrix.PSL3Four.InnerFamilyNormalizer.Centerless
open Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer

/-- The whole quartic graph-field fixed group has two-rank at most one. -/
theorem quartic_graphField_fixed_rank : primeRank 2 graphField.fixedSubgroup ≤ 1 := by
  let P : Sylow 2 graphField.fixedSubgroup :=
    Sylow.ofCard (quaternion.subgroupOf graphField.fixedSubgroup) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe quaternion_le_fixed).toEquiv,
        quaternion_card, fixed_card]
      decide +kernel)
  obtain ⟨eQ⟩ := quaternion_equiv
  let e : P ≃* QuaternionGroup 2 :=
    (subgroupOfEquivOfLe quaternion_le_fixed).trans eQ
  exact (P.primeRank_eq.trans (primeRank_equiv 2 e)).le.trans quaternion_rank

variable {F : Type*} [Field F] [Finite F]

/-- Transport uses an actual identification of both the group and actor. -/
theorem quartic_fixed_rank_of_congr
    (e : PSL(3,F) ≃* Matrix.PSL3Four.PSL) (a : MulAut PSL(3,F))
    (ha : MulAut.congr e a = graphField) : primeRank 2 a.fixedSubgroup ≤ 1 := by
  rw [primeRank_equiv 2 (MulAut.fixedSubgroupCongr e a), ha]
  exact quartic_graphField_fixed_rank

/-- Application to the sharp quartic actor bound, with only the independent
outer-image bound and literal actor identification still explicit. -/
theorem quartic_actor_rank_le_three
    (e : PSL(3,F) ≃* Matrix.PSL3Four.PSL)
    (E : Subgroup (MulAut PSL(3,F))) [IsElementaryAbelian 2 E]
    (a : MulAut PSL(3,F)) (ha : a ∈ E) (he : MulAut.congr e a = graphField)
    (houter : primeRank 2
      (E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))) ≤ 2) :
    Group.rank E ≤ 3 :=
  (rank_le_fixed_add_outer E a ha).trans
    (Nat.add_le_add (quartic_fixed_rank_of_congr e a he) houter)

end Matrix.PSL3Even.OuterElementaryRank
