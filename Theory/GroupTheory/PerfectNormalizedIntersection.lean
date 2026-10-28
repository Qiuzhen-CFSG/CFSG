module
public import Theory.GroupTheory.Commutator.SimpleSubnormal
/-!
# Perfect centralization from a normalized intersection

If the commutator of Q with a perfect L lies in Q∩K, and that intersection
normalizes L, disjointness of Q and L makes the second commutator vanish.
Perfectness then gives centralization. Relative normalization suffices.

Source: the three-subgroup step in Aschbacher–Smith 2.4.7, printed p.541.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Once the normal core misses L, containment of its component
intersection in a normalizer makes the perfect block centralize the core. -/
theorem centralizes_of_normalized_intersection_bot
    (Q K L B : Subgroup G) [Group.IsPerfect L]
    (hLQ : L ≤ normalizer (Q : Set G)) (hQK : Q ≤ normalizer (K : Set G))
    (hLK : L ≤ K) (hQL : Q ⊓ L = ⊥) (hQB : Q ⊓ K ≤ B)
    (hBL : B ≤ normalizer (L : Set G)) : L ≤ centralizer (Q : Set G) := by
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_eq_bot_of_iterated_eq_bot
  apply bot_unique
  rw [←hQL]
  have hcomm : ⁅Q,L⁆ ≤ Q ⊓ K := le_inf
    (le_normalizer_iff_commutator_le_left.mp hLQ)
    ((commutator_mono le_rfl hLK).trans (le_normalizer_iff_commutator_le_right.mp hQK))
  exact le_inf
    ((commutator_mono (hcomm.trans inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hLQ))
    (le_normalizer_iff_commutator_le_right.mp (hcomm.trans (hQB.trans hBL)))

end Subgroup
