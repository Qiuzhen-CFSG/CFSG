module

public import Theory.GroupTheory.TwoInvolutionClassLocalBounds.Transport

/-!
# A refined Thompson order bound from a local conjugacy cover

Let `z,t` represent the two involution classes of a finite group. Inside the
full centralizer of `z`, bound the two product slices with product in the
`z` class, and cover the `t,t` slice by local conjugacy classes. Exchanging
marked commuting pairs transports that cover to the full centralizer of
`t`; its orbit sizes scale by the ratio of the centralizer orders. Dihedral
exchange takes the second Thompson fiber into pairs in the same local
class, bounded by the sum of the squares of the transported class bounds.
No disjointness, separation, or exact local class sizes are assumed.

Source motivation: Aschbacher–Smith, combined manuscript (1 March 2004),
A.6.1–4, printed pp. 64–65. The second fiber at `z` is actually bounded
by the square of the mixed slice size, a strengthening of the usual
`b₂(z)c₂(z) = (c₂(z)+1)c₂(z)` estimate used in the displayed conclusion.
-/

public section
namespace Theory.GroupTheory.TwoInvolutionClassLocalBounds
open scoped BigOperators
variable {G : Type*} [Group G] [Finite G]

/-- The refined Thompson bound from an overlapping local conjugacy cover.
`Slice z z z`, `Slice z t z`, and `Slice z t t` are respectively the sets
`X`, `Y`, and `W`. Each representative belongs to `W`; the conjugacy in
the cover and the class cardinality bound are inside the full `C_G(z)`.
The last count bounds all ambient `t`-conjugates in the full `C_G(t)`. -/
theorem card_le_of_local_conjugacy_cover {ι : Type*} [Fintype ι]
    (z t : G) (hz : orderOf z = 2) (ht : orderOf t = 2) (hn : ¬ IsConj z t)
    (hclasses : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj t u)
    (r bz bt d : ℕ) (n : ι → ℕ) (hr : 0 < r)
    (hcard : Nat.card (Centralizer z) = r * Nat.card (Centralizer t))
    (hX : Nat.card (Slice z z z) ≤ bz)
    (hY : Nat.card (Slice z t z) ≤ r * d)
    (w : ι → Slice z t t)
    (hcover : ∀ u : Slice z t t, ∃ i, IsConj (w i).val u.val)
    (hbound : ∀ i, Nat.card (LocalOrbit (w i).val) ≤ r * n i)
    (htcount : Nat.card {u : Centralizer t // IsConj t (u : G)} ≤ bt) :
    Nat.card G ≤ Nat.card (Centralizer t) *
      (bz * (r * ∑ i, n i) + (r*d+1)*(r*d) + r*(bt*d + ∑ i, (n i)^2)) := by
  obtain ⟨v, hvcover, hvbound⟩ := exists_transported_cover ht w n hr hcard hcover hbound
  exact card_le_of_two_local_covers z t hz ht hn hclasses r bz bt d n hr hcard
    hX hY htcount (fun i => (w i).val) hcover hbound (fun i => (v i).val) hvcover hvbound

end Theory.GroupTheory.TwoInvolutionClassLocalBounds
end
