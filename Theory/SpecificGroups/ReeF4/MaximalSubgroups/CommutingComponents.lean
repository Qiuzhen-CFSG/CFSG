module

public import Theory.SpecificGroups.ReeF4.Model
public import BenderSuzuki.MatrixGroups.Suzuki
public import Theory.GroupTheory.CComponent.RadicalFreeProduct
public import Mathlib.GroupTheory.IndexNormal

/-!
# The Suzuki-product route for Ree maximal subgroups

Two geometric obligations remain for a radical-free maximal subgroup of the
genuine Ree group with distinct commuting components: identify their carriers
as Sz(q), and establish index two for their join. The second obligation may
use actual carrier equivalences supplied by the first; it assumes neither
normality nor that there are exactly two components. These definitions are
proof obligations, not an asserted classification.

The finite-group assembly below constructs the product equivalence by
multiplication. Index two supplies normality inside the maximal subgroup and
the exact quotient order. No ambient normality or splitting is required.

Source: Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52--69, DOI 10.1016/0021-8693(91)90283-E. The Sz(q)≀2 entry is reproduced
in the unconditional list inside the proof of Theorem 5 of arXiv:0910.4758,
pp.2--3. Here q denotes the field size 2^(2*m+1).
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.CommutingComponents

open Subgroup BenderSuzuki.MatrixGroups

/-- Identify a supplied component in the multiple-component maximal-subgroup
case. Interchanging the two components identifies the second one. -/
def ComponentCarrierIdentification : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ L K : Subgroup M,
      L.IsCComponent → K.IsCComponent → L ≠ K → ⁅L, K⁆ = ⊥ →
        Nonempty (L ≃* SuzukiMatrixGroup m)

/-- The geometric index calculation, conditional on the actual Suzuki
carrier identifications. Normality and the number of components are not inputs. -/
def IdentifiedPairIndex : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ L K : Subgroup M,
      L.IsCComponent → K.IsCComponent → L ≠ K → ⁅L, K⁆ = ⊥ →
        (L ≃* SuzukiMatrixGroup m) → (K ≃* SuzukiMatrixGroup m) → (L ⊔ K).index = 2

/-- The normal subgroup is the actual join of the supplied components.
Its product isomorphism and quotient order follow from the displayed inputs. -/
theorem normal_suzuki_product_of_index_two
    {m : ℕ} {H : Type*} [Group H] [Finite H] {L K : Subgroup H}
    (hR : solvableRadical H = ⊥) (hL : L.IsCComponent) (hc : ⁅L, K⁆ = ⊥)
    (eL : L ≃* SuzukiMatrixGroup m) (eK : K ≃* SuzukiMatrixGroup m)
    (hi : (L ⊔ K).index = 2) :
    (L ⊔ K).Normal ∧
      Nonempty (↥(L ⊔ K) ≃* (SuzukiMatrixGroup m × SuzukiMatrixGroup m)) ∧
      Nat.card (H ⧸ (L ⊔ K)) = 2 := by
  obtain ⟨e, _⟩ := hL.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hR hc
  exact ⟨normal_of_index_eq_two hi,
    ⟨e.symm.trans (eL.prodCongr eK)⟩, (L ⊔ K).index_eq_card.symm.trans hi⟩

end ReeF4.MaximalSubgroups.CommutingComponents
