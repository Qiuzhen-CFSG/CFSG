module

public import Mathlib.GroupTheory.Index

/-!
# Cardinalities of kernels in a commuting triangle

A surjection between groups over the same base restricts to a surjection
between their kernels. Consequently the target kernel order divides the source
kernel order. This is the elementary cardinality step used to transfer Schur
multiplier bounds to individual central covers (GLS3, Corollary 5.1.5).
-/

namespace Theory.GroupTheory

/-- In a commuting triangle whose map between covering groups is onto,
the lower kernel is a quotient of the upper kernel. -/
public theorem kernel_card_dvd_of_surjective_factor
    {L G K : Type*} [Group L] [Group G] [Group K]
    (f : L →* K) (g : G →* K) (h : L →* G)
    (hsurj : Function.Surjective h) (hfac : g.comp h = f) :
    Nat.card g.ker ∣ Nat.card f.ker := by
  have heq : f.ker.map h = g.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g (h y) = 1
      rw [← MonoidHom.comp_apply, hfac]
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := hsurj x
      refine ⟨y, ?_, rfl⟩
      change f y = 1
      rw [← hfac]
      exact hx
  rw [← heq]
  exact Subgroup.card_map_dvd _ _

end Theory.GroupTheory

