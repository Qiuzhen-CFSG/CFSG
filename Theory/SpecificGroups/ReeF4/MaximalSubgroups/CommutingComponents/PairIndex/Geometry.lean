module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents

/-!
# Geometric inputs for the Suzuki-pair index calculation

The factor-normalizer bound and the ambient factor interchange are independent
Ree geometry obligations. The finite-group argument derives the centralizer
bound, the fact that there are only two components, and normality of their join.
Maximality then puts the ambient interchange in the given maximal subgroup.

Neither definition asserts a theorem. In particular, the ambient normalizer
must be proved proper, and the interchange must act on the actual embedded
factors. No order-two representative or splitting is requested.

Source: Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52--69, DOI 10.1016/0021-8693(91)90283-E; the Sz(q)≀2 entry reproduced in
the proof of Theorem 5 of arXiv:0910.4758, pp.2--3. Here q = 2^(2*m+1).
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.CommutingComponents

open Subgroup BenderSuzuki.MatrixGroups

/-- An element of the maximal subgroup normalizing the first identified
Suzuki component belongs to the product of the two components. -/
def IdentifiedFactorNormalizer : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ L K : Subgroup M,
      L.IsCComponent → K.IsCComponent → L ≠ K → ⁅L, K⁆ = ⊥ →
        (L ≃* SuzukiMatrixGroup m) → (K ≃* SuzukiMatrixGroup m) →
          normalizer (L : Set M) ≤ L ⊔ K

/-- The actual embedded join has a proper ambient normalizer containing an
element interchanging its two specified factors. This assumes no relative
normality and does not assert that the element has order two. -/
def IdentifiedPairSwap : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ L K : Subgroup M,
      L.IsCComponent → K.IsCComponent → L ≠ K → ⁅L, K⁆ = ⊥ →
        (L ≃* SuzukiMatrixGroup m) → (K ≃* SuzukiMatrixGroup m) →
          normalizer (((L ⊔ K).map M.subtype) : Set (Model m)) ≠ ⊤ ∧
            ∃ s : Model m,
              (L.map M.subtype).map (MulAut.conj s).toMonoidHom = K.map M.subtype ∧
              (K.map M.subtype).map (MulAut.conj s).toMonoidHom = L.map M.subtype

end ReeF4.MaximalSubgroups.CommutingComponents
