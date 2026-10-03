module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Coset actions of simple groups

The normal core of a proper subgroup of a simple group is trivial. Therefore
the coset action is faithful, and in the finite case the group order divides
the factorial of the subgroup index.

This gives the elementary small-index obstruction used in Wong (1964),
Theorem 6(b), p.110.
-/

namespace Subgroup

variable {G : Type*} [Group G] [IsSimpleGroup G]

/-- A proper subgroup of a simple group has trivial normal core. -/
public theorem normalCore_eq_bot_of_simple (H : Subgroup G) (hH : H ≠ ⊤) :
    H.normalCore = ⊥ := by
  rcases H.normalCore_normal.eq_bot_or_eq_top with h | h
  · exact h
  · exact (hH (top_le_iff.mp (h ▸ H.normalCore_le))).elim

/-- The natural coset action of a simple group on a proper subgroup is faithful. -/
public theorem faithfulSMul_quotient_of_simple (H : Subgroup G) (hH : H ≠ ⊤) :
    FaithfulSMul G (G ⧸ H) := by
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← H.normalCore_eq_ker]
    exact H.normalCore_eq_bot_of_simple hH
  apply faithfulSMul_iff.mpr
  intro g hg
  apply hinj
  ext x
  simpa using hg x

/-- A finite simple group embeds in the symmetric group on the cosets of
each proper subgroup. -/
public theorem card_dvd_factorial_index_of_simple [Finite G]
    (H : Subgroup G) (hH : H ≠ ⊤) : Nat.card G ∣ H.index.factorial := by
  have hd : H.normalCore.index ∣ H.index.factorial := by
    rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
    exact card_subgroup_dvd_card (MulAction.toPermHom G (G ⧸ H)).range
  rwa [H.normalCore_eq_bot_of_simple hH, index_bot] at hd

end Subgroup
