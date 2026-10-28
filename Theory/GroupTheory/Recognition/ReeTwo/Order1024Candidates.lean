module

public import Theory.GroupTheory.Recognition.ReeTwo.LargeCentricCandidates
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024Representatives
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024Enumeration
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024ExceptionalObstructions
public import Theory.SpecificGroups.ReeTwo.CoreCharacterKernel

/-!
# Classification of Ree two centric radical candidates of order 1024

Every subgroup of order 1024 in the order-4096 Sylow model has index four
and contains the six-root tail. If it is contained in the canonical core,
equality follows by comparing orders. A centric radical subgroup of this
order cannot have a two-group automorphism group.

The checked enumeration leaves the canonical core, candidates with two-group
automorphism groups, and three exceptional conjugacy classes. The first
automorphism obstruction excludes the two-group cases; explicit non-inner
normalizer actions in the automorphism two-core exclude the exceptions.
Thus every centric radical candidate of order 1024 is the canonical core.
The enumeration includes candidates inside the parity kernel.

Source: Shinoda (1975), (2.3), pp. 81–82, for the verified group model;
the tail argument is proved in `ReeTwo.SylowTail`.
-/

namespace ReeTwo.SylowModel

/-- Order 1024 is equivalent here to index four. -/
public theorem index_eq_four_of_card_eq_1024 (U : Subgroup SylowModel)
    (hU : Nat.card U = 1024) : U.index = 4 := by
  have h := U.index_mul_card
  rw [hU, card] at h
  omega

/-- Tail containment holds for all order-1024 subgroups, including those in
the parity kernel, with no centricity or radicality assumption. -/
public theorem tailSubgroup_le_of_card_eq_1024 (U : Subgroup SylowModel)
    (hU : Nat.card U = 1024) : tailSubgroup ≤ U :=
  tailSubgroup_le_of_index_eq_four U (index_eq_four_of_card_eq_1024 U hU)

/-- Once containment in the canonical core is known, the orders force equality. -/
public theorem eq_coreSubgroup_of_le_of_card_eq_1024 (U : Subgroup SylowModel)
    (hle : U ≤ coreSubgroup) (hU : Nat.card U = 1024) : U = coreSubgroup :=
  Subgroup.eq_of_le_of_card_ge hle (by rw [hU, coreSubgroup_card])

/-- The easy automorphism case is excluded at order 1024. -/
public theorem not_isPGroup_mulAut_of_centric_radical_of_card_eq_1024
    (U : Subgroup SylowModel)
    (hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hr : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hU : Nat.card U = 1024) : ¬ IsPGroup 2 (MulAut U) := by
  intro ha
  have ht := eq_top_of_centric_radical_of_isPGroup_mulAut U hc hr ha
  rw [ht, Subgroup.card_top, card] at hU
  contradiction

/-- The canonical core is the only intrinsic centric radical subgroup of
order 1024 in the Ree two Sylow model. -/
public theorem centric_radical_eq_coreSubgroup_of_card_eq_1024
    (U : Subgroup SylowModel)
    (hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hr : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hU : Nat.card U = 1024) : U = coreSubgroup := by
  rcases residualEnumeration U hc hU with hcore | ha | ⟨i, g, rfl⟩
  · exact hcore
  · exact (not_isPGroup_mulAut_of_centric_radical_of_card_eq_1024 U hc hr hU ha).elim
  · exact (exceptionalCandidate_map_conj_not_intrinsic_radical i g hr).elim

end ReeTwo.SylowModel
