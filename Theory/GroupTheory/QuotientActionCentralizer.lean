module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index

/-!
# Fixed subgroups for quotient conjugation actions

If a normal subgroup `Q` centralizes `V`, conjugation on `V` factors through
`G/Q`. The fixed subgroup of a subgroup of this quotient is the centralizer
in `V` of its full preimage. For an image subgroup this agrees with the
centralizer of the original subgroup. We also compare image orders when one
homomorphism has a larger kernel.

These are the quotient-action bridges used in Aschbacher–Smith, *The
Classification of Quasithin Groups*, Lemma E.5.5 (printed p.244).
-/

namespace Subgroup
variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- The fixed subgroup in `V` of `B ≤ G/Q`, computed using its full preimage.
When `V` is normal and `Q ≤ C_G(V)`, this is `C_V(B)` for quotient conjugation. -/
@[expose] public def quotientActionCentralizer (V Q : Subgroup G) [Q.Normal]
    (B : Subgroup (G ⧸ Q)) : Subgroup G :=
  V ⊓ centralizer (B.comap (QuotientGroup.mk' Q) : Set G)

/-- Fixed elements belong to the group on which the quotient acts. -/
public theorem quotientActionCentralizer_le (V Q : Subgroup G) [Q.Normal]
    (B : Subgroup (G ⧸ Q)) : quotientActionCentralizer V Q B ≤ V := inf_le_left

/-- Passing to the quotient image does not change the fixed subgroup. -/
public theorem quotientActionCentralizer_image (V Q A : Subgroup G) [Q.Normal]
    (hQ : Q ≤ centralizer (V : Set G)) :
    quotientActionCentralizer V Q (A.map (QuotientGroup.mk' Q)) =
      V ⊓ centralizer (A : Set G) := by
  rw [quotientActionCentralizer, comap_map_eq, QuotientGroup.ker_mk']
  refine le_antisymm
    (inf_le_inf_left V (centralizer_le (show A ≤ A ⊔ Q from le_sup_left))) ?_
  refine le_inf inf_le_left (le_centralizer_iff.mpr (sup_le ?_ ?_))
  · exact le_centralizer_iff.mp inf_le_right
  · exact hQ.trans (centralizer_le
      (show V ⊓ centralizer (A : Set G) ≤ V from inf_le_left))

/-- A larger kernel gives an image of no larger order. -/
public theorem card_map_le_card_map_of_ker_le [Finite K]
    (A : Subgroup G) (f : G →* H) (g : G →* K) (hker : g.ker ≤ f.ker) :
    Nat.card (A.map f) ≤ Nat.card (A.map g) := by
  have hd := relIndex_dvd_of_le_left A hker
  rw [relIndex_ker, relIndex_ker] at hd
  exact Nat.le_of_dvd Nat.card_pos hd

end Subgroup
