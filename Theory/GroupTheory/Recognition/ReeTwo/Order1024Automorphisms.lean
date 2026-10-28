module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024ResidualRepresentatives
public import Theory.GroupTheory.PGroup.FrattiniProfile
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfiles
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedProfiles

/-!
# Two-group automorphisms of the fifteen residual Ree two representatives

Each representative is a two-group, being a subgroup of the explicit Sylow
model. The Frattini-profile criterion reduces its automorphism problem to
an explicit small quotient: counts of intrinsic labels in the quotient
fibers are preserved by every automorphism, and the kernel of the quotient
action is a two-group.

The checked finite profile calculations in `Order1024OrderProfiles` and
`Order1024RefinedProfiles` discharge the two batches of the assembly lemma.
Indices 1, 5, 7, and 13 use centralizer orders to refine element-order profiles;
element-order profiles suffice for the other eleven indices. Thus all fifteen
specified representatives, including the parity-kernel representatives, have
two-group automorphism groups, independently of any subgroup census.

Source: Shinoda (1975), (2.3), pp. 81–82, for the coordinate model;
the automorphism reduction is the Burnside basis-kernel argument in
`Theory.GroupTheory.PGroup.FrattiniProfile`.
-/

namespace ReeTwo.SylowModel

/-- Every specified residual representative is a two-group. -/
public theorem residualCandidate_isPGroup (i : Fin 15) :
    IsPGroup 2 (residualCandidate i) :=
  (IsPGroup.of_card (n := 12) card).to_subgroup (residualCandidate i)

/-- An explicit Frattini quotient and a verified intrinsic-label profile
certificate suffice for any of the fifteen representatives. -/
public theorem residualCandidate_isPGroup_mulAut_of_frattini_profile
    (i : Fin 15) {Q A : Type*} [Group Q]
    (e : ((residualCandidate i) ⧸ frattini (residualCandidate i)) ≃* Q)
    (label : residualCandidate i → A)
    (hl : ∀ (f : MulAut (residualCandidate i)) x, label (f x) = label x)
    (cert : ∀ b : MulAut Q,
      (∀ y, Subgroup.fiberProfile
          (fun x => e (QuotientGroup.mk' (frattini (residualCandidate i)) x)) label (b y) =
        Subgroup.fiberProfile
          (fun x => e (QuotientGroup.mk' (frattini (residualCandidate i)) x)) label y) →
      ∃ k : ℕ, b ^ (2 ^ k) = 1) :
    IsPGroup 2 (MulAut (residualCandidate i)) :=
  Subgroup.isPGroup_mulAut_of_frattini_profile (residualCandidate_isPGroup i) e label hl cert

/-- Assemble the order-profile and refined-profile batches without any census
or conjugacy assumption. Both batches are explicit mathematical hypotheses. -/
public theorem residualCandidate_isPGroup_mulAut_of_partition
    (hOrder : ∀ i : Fin 15, i ≠ 1 → i ≠ 5 → i ≠ 7 → i ≠ 13 →
      IsPGroup 2 (MulAut (residualCandidate i)))
    (hRefined : ∀ i : Fin 15, i = 1 ∨ i = 5 ∨ i = 7 ∨ i = 13 →
      IsPGroup 2 (MulAut (residualCandidate i))) :
    ∀ i : Fin 15, IsPGroup 2 (MulAut (residualCandidate i)) := by
  intro i
  by_cases h1 : i = 1
  · exact hRefined i (Or.inl h1)
  by_cases h5 : i = 5
  · exact hRefined i (Or.inr (Or.inl h5))
  by_cases h7 : i = 7
  · exact hRefined i (Or.inr (Or.inr (Or.inl h7)))
  by_cases h13 : i = 13
  · exact hRefined i (Or.inr (Or.inr (Or.inr h13)))
  exact hOrder i h1 h5 h7 h13

/-- All fifteen explicit residual representatives have two-group automorphism
groups. The order-profile and refined-profile certificates cover every index,
without a census or conjugacy hypothesis. -/
public theorem residualCandidate_isPGroup_mulAut :
    ∀ i : Fin 15, IsPGroup 2 (MulAut (residualCandidate i)) :=
  residualCandidate_isPGroup_mulAut_of_partition
    residualCandidate_orderProfile_isPGroup_mulAut
    residualCandidate_refinedProfile_isPGroup_mulAut

end ReeTwo.SylowModel
