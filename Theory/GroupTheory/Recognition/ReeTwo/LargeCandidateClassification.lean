module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024Candidates
public import Theory.GroupTheory.Recognition.ReeTwo.Order2048Candidates

/-!
# Large intrinsic centric radical candidates in the Ree two Sylow model

A centric subgroup of order at least 1024 whose normalizer action intersects
the automorphism two-core only in inner automorphisms is the whole Sylow
model, the first parabolic core, or the canonical order-1024 core.

Lagrange's theorem reduces a proper subgroup to order 2048 or 1024. The
classification at each order then identifies its unique candidate. Both
order classifications include subgroups contained in the parity kernel.

Source: van Beek (2024), Proposition 3.1, p. 10, motivates the candidate
classification. The order-specific proofs use the verified Shinoda (1975)
model and the intrinsic automorphism calculations cited in
`Order1024Candidates` and `Order2048Candidates`.
-/

namespace ReeTwo.SylowModel

/-- Every large intrinsic centric radical candidate is the whole model,
the first parabolic core, or the canonical core. -/
public theorem large_centric_radical_classification (U : Subgroup SylowModel)
    (hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hr : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hU : 1024 ≤ Nat.card U) :
    U = ⊤ ∨ U = firstParabolicCore ∨ U = coreSubgroup := by
  rcases large_subgroup_cases U hU with ht | h | h
  · exact Or.inl ht
  · exact Or.inr (Or.inl
      (centric_radical_eq_firstParabolicCore_of_card_eq_2048 U hc hr h))
  · exact Or.inr (Or.inr
      (centric_radical_eq_coreSubgroup_of_card_eq_1024 U hc hr h))

end ReeTwo.SylowModel
