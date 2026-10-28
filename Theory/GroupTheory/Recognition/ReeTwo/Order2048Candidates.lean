module

public import Theory.GroupTheory.Recognition.ReeTwo.LargeCentricCandidates
public import Theory.SpecificGroups.ReeTwo.FirstParabolicCoordinates
public import Theory.SpecificGroups.ReeTwo.MaximalCoreAutomorphisms
public import Theory.SpecificGroups.ReeTwo.MaximalParityAutomorphisms

/-!
# Explicit order-2048 Ree two candidates

The seven index-two subgroups are kernels of the binary characters in
`MaximalCharacters`. The parameter `(0,1,0)` is the first parabolic core.
The remaining six split into two kernels with a parity coefficient and
four kernels with a core-character coefficient. An intrinsic centric
radical candidate in either family must have an automorphism group which
is not a two-group.

The automorphism theorems for the two families show that all six have
two-group automorphism groups, excluding them and leaving precisely the
first parabolic core.
Source: the coordinate enumeration and first-parabolic identification in
`MaximalCharacters` and `FirstParabolicCoordinates`, with the intrinsic
normalizer reduction from `LargeCentricCandidates` and the automorphism
calculations in `MaximalCoreAutomorphisms` and `MaximalParityAutomorphisms`.
-/

namespace ReeTwo.SylowModel

/-- Explicit alternatives for an intrinsic centric radical candidate of order
2048. The two residual families include the parity kernel. -/
public theorem centric_radical_order2048_cases (U : Subgroup SylowModel)
    (hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hr : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hU : Nat.card U = 2048) :
    U = firstParabolicCore ∨
      (∃ b : ZMod 2, U = (maximalCharacter 1 b 0).ker ∧ ¬ IsPGroup 2 (MulAut U)) ∨
      (∃ a b : ZMod 2, U = (maximalCharacter a b 1).ker ∧ ¬ IsPGroup 2 (MulAut U)) := by
  have hnot : ¬ IsPGroup 2 (MulAut U) := by
    intro h
    have he := eq_top_of_centric_radical_of_isPGroup_mulAut U hc hr h
    have hcard : Nat.card U = 4096 := by
      rw [he, Nat.card_congr Subgroup.topEquiv.toEquiv, card]
    omega
  obtain ⟨a, b, c, hne, he⟩ := eq_maximalCharacter_ker_of_index_eq_two U
    (index_eq_two_of_card_eq_2048 U hU)
  have hbin : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases hbin c with rfl | rfl
  · rcases hbin a with rfl | rfl
    · have hb : b = 1 := (hbin b).resolve_left (by simpa using hne)
      subst b
      exact Or.inl (he.trans firstParabolicCore_eq_maximalCharacter_ker.symm)
    · exact Or.inr (Or.inl ⟨b, he, hnot⟩)
  · exact Or.inr (Or.inr ⟨a, b, he, hnot⟩)

/-- An intrinsic centric radical subgroup of order 2048 is the first
parabolic core. -/
public theorem centric_radical_eq_firstParabolicCore_of_card_eq_2048
    (U : Subgroup SylowModel)
    (hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hr : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hU : Nat.card U = 2048) : U = firstParabolicCore := by
  rcases centric_radical_order2048_cases U hc hr hU with h | ⟨b, he, hn⟩ | ⟨a, b, he, hn⟩
  · exact h
  · subst U
    exact (hn (maximalParity_isPGroup_mulAut b)).elim
  · subst U
    exact (hn (maximalCore_isPGroup_mulAut a b)).elim

end ReeTwo.SylowModel
