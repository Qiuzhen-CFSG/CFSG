module

public import Stellmacher.SectionEleven.C2S4CentralizerMaximal
public import Stellmacher.SectionEleven.C2S4NormalizerThompson
public import Stellmacher.ElementaryAbelianMaxJNormalizerClosure

/-!
# The order-thirty-two terminal case of Section 11

For a non-Sylow Hypothesis Two pair with `P1 ≃ C₂ × S₄` and
`N_H(O₂(P1)) = P1`, the centralizer/maximality theorem first proves that
`C_H(Z(P1)) = P1` and that `P1` is maximal two-local. The elementary-pair
calculation then gives order thirty-two and elementary Thompson subgroup `S`
for `N_{S0}(S)`. Automorphism invariance of the Thompson subgroup and the
normalizer condition in the finite two-group `S0` force `N_{S0}(S) = S0`.
The witness for the maximal-two-local conclusion is `P1` itself.

This assembles case (II) of Stellmacher Section 11 into alternative (c) of
Theorem 2. The displayed model and two-core normalizer equality are explicit
inputs; no classification placeholder or additional local hypothesis is used.
Source: `refs/latex/stellmacher-n-group.tex`, Section 11, case (II).
-/

namespace Stellmacher.SectionEleven

/-- The `C₂ × S₄` case of the unique-maximal branch gives alternative (c). -/
public theorem unique_order32_terminal
    {H : Type*} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : SectionsFiveToSeven.HypothesisTwo H S0 S P1 P2)
    (hne : S ≠ (S0 : Subgroup H))
    (hModel : Later.IsModel P1 (Later.C2 × Later.S4))
    (hNormalizer : Subgroup.normalizer
      (SectionsFiveToSeven.twoCoreIn P1 : Set H) = P1) :
    Nat.card S0 = 2 ^ 5 ∧ ∃ U : Subgroup H,
      IsMaximalTwoLocal U ∧
        Nonempty (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) := by
  obtain ⟨hCentralizer, hMaximal⟩ :=
    c2s4_centralizer_maximal S0 S P1 P2 h hne hModel hNormalizer
  obtain ⟨hCard, hThompson⟩ :=
    c2s4_normalizer_thompson S0 S P1 P2 h hne hModel hNormalizer hCentralizer
  let : Group.IsNilpotent (S0 : Subgroup H) := S0.isPGroup'.isNilpotent
  have hSylow := inf_normalizer_eq_of_thompson_eq (S0 : Subgroup H) S
    Group.normalizerCondition_of_isNilpotent hThompson
  exact ⟨by simpa only [hSylow] using hCard, P1, hMaximal, hModel⟩

end Stellmacher.SectionEleven
