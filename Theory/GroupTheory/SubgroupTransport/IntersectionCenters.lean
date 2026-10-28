module
public import Theory.GroupTheory.SubgroupTransport.IntersectionLattice

/-!
# Centers recovered from an abelian intersection diagonal

If adjacent cells reconstruct a strip, centralization propagates from its
terminal diagonal to its root. When that diagonal is abelian and its two
endpoints contain the root center, their intersection is exactly the center.
In applications, maximum abelian order supplies the endpoint containments.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(d),(e),
printed page 46. The argument uses only the actual partial isomorphism and
subgroup joins, with no ambient automorphism extension.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

/-- Centralization propagates from a diagonal to its root whenever the
intervening adjacent cells reconstruct by joins. -/
theorem intervalCell_le_centralizer_of_diagonal (φ : S ≃* T) (C : Subgroup G)
    (a b n : ℕ)
    (hcomm : ∀ i j : ℕ, i + j = n →
      intervalCell φ (a + i) (b + j) ≤ centralizer (C : Set G))
    (hgen : ∀ i j : ℕ, i + j < n →
      intervalCell φ (a + i) (b + j + 1) ⊔ intervalCell φ (a + i + 1) (b + j) =
        intervalCell φ (a + i) (b + j)) :
    intervalCell φ a b ≤ centralizer (C : Set G) := by
  have key : ∀ k i j : ℕ, i + j + k = n →
      intervalCell φ (a + i) (b + j) ≤ centralizer (C : Set G) := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      exact hcomm i j (by omega)
    | succ k ih =>
      intro i j hij
      rw [← hgen i j (by omega)]
      refine sup_le ?_ ?_
      · simpa only [Nat.add_assoc] using ih i (j + 1) (by omega)
      · simpa only [Nat.add_assoc] using ih (i + 1) j (by omega)
  simpa only [Nat.add_zero] using key n 0 0 (by omega)

/-- The two terminal endpoint cells determine the center of their root.
Containment of the root center in the endpoints is supplied in applications
by maximum abelian order. -/
theorem intervalCell_center_eq (φ : S ≃* T) (a b n : ℕ)
    (hleft : intervalCell φ a b ⊓ centralizer (intervalCell φ a b : Set G) ≤
      intervalCell φ a (b + n))
    (hright : intervalCell φ a b ⊓ centralizer (intervalCell φ a b : Set G) ≤
      intervalCell φ (a + n) b)
    (habelian : ∀ i j : ℕ, i + j = n →
      IsMulCommutative (intervalCell φ (a + i) (b + j)))
    (hgen : ∀ i j : ℕ, i + j < n →
      intervalCell φ (a + i) (b + j + 1) ⊔ intervalCell φ (a + i + 1) (b + j) =
        intervalCell φ (a + i) (b + j)) :
    intervalCell φ a b ⊓ centralizer (intervalCell φ a b : Set G) =
      intervalCell φ (a + n) (b + n) := by
  apply le_antisymm
  · have hh := le_inf hleft hright
    rw [intervalCell_inf, max_eq_right (show a ≤ a + n by omega),
      max_eq_left (show b ≤ b + n by omega)] at hh
    exact hh
  · refine le_inf (intervalCell_antitone φ (by omega) (by omega)) ?_
    apply le_centralizer_iff.mpr
    apply intervalCell_le_centralizer_of_diagonal φ _ a b n _ hgen
    intro i j hij
    let _ := habelian i j hij
    exact (intervalCell φ (a + i) (b + j)).le_centralizer.trans
      (centralizer_le (intervalCell_antitone φ (by omega) (by omega)))

end Theory.GroupTheory.SubgroupTransport
