module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileData
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileRankTwo
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileRankThree
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileRankFour

/-!
# Order-profile reduction for the residual Ree two automorphism groups

A concrete Frattini quotient with the specified order profiles has
profile-preserving automorphisms of exponent dividing four, by
`Order1024OrderProfileData`. The Burnside basis-kernel theorem then makes
the full automorphism group a two-group. The concrete quotient models of ranks
two, three and four establish this assertion for all eleven representatives
outside indices 1, 5, 7 and 13, independently of census exhaustiveness.

Source: the intrinsic profile argument in `PGroup.FrattiniProfile` and the
Shinoda coordinate convention recorded in `Order1024OrderProfileData`.
-/

namespace ReeTwo.SylowModel

/-- A verified concrete order-profile model proves the automorphism assertion. -/
public theorem residualCandidate_orderProfile_isPGroup_mulAut_of_model
    (i : Fin 15) (h1 : i ≠ 1) (h5 : i ≠ 5) (h7 : i ≠ 7) (h13 : i ≠ 13)
    (hm : OrderProfileModel i) : IsPGroup 2 (MulAut (residualCandidate i)) := by
  obtain ⟨π, hπ, hker, hcolor⟩ := hm
  let e : ((residualCandidate i) ⧸ frattini (residualCandidate i)) ≃*
      OrderProfileQuotient (orderProfileRank i) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  apply Subgroup.isPGroup_mulAut_of_frattini_profile
    ((IsPGroup.of_card (n := 12) card).to_subgroup (residualCandidate i))
    e orderOf Subgroup.orderOf_mulAut
  intro b hb
  refine ⟨2, orderProfileColor_aut_four i h1 h5 h7 h13 b ?_⟩
  intro x
  exact hcolor (b x) x (hb x)

/-- The eleven residual candidates distinguished by their Frattini element-order
profiles have two-group automorphism groups. -/
public theorem residualCandidate_orderProfile_isPGroup_mulAut
    (i : Fin 15) (h1 : i ≠ 1) (h5 : i ≠ 5) (h7 : i ≠ 7) (h13 : i ≠ 13) :
    IsPGroup 2 (MulAut (residualCandidate i)) := by
  apply residualCandidate_orderProfile_isPGroup_mulAut_of_model i h1 h5 h7 h13
  by_cases htwo : i = 10 ∨ i = 11 ∨ i = 14
  · exact orderProfileModel_rankTwo i htwo
  by_cases hthree : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 8
  · exact orderProfileModel_rankThree i hthree
  exact orderProfileModel_rankFour i (by omega)

end ReeTwo.SylowModel
