module

public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore

/-!
# Detecting centralizers on the central omega of a two-group

If a finite two-group P normalizes Y, its centralizer of Y is normal in P.
A nontrivial such centralizer meets the first omega of the center of P.
Consequently triviality can be checked on central involutions alone.
-/

public section
namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A normalized actor with no fixed point on the central omega has trivial
centralizer in the whole two-group. -/
theorem inf_centralizer_eq_bot_of_omegaCenterIn_inf_eq_bot
    (P Y : Subgroup G) (hP : IsPGroup 2 P)
    (hPY : P ≤ normalizer (Y : Set G))
    (hfixed : omegaCenterIn P ⊓ centralizer (Y : Set G) = ⊥) :
    P ⊓ centralizer (Y : Set G) = ⊥ := by
  by_contra hne
  have hn : P ≤ normalizer (P ⊓ centralizer (Y : Set G) : Set G) :=
    (le_inf P.le_normalizer (hPY.trans (normalizer_le_normalizer_centralizer Y))).trans
      inf_normalizer_le_normalizer_inf
  apply inf_omegaCenterIn_ne_bot_of_normalized_twoGroup
    (P ⊓ centralizer (Y : Set G)) P inf_le_left hP hn hne
  apply bot_unique
  exact (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans_eq hfixed

/-- Pointwise form of central-omega detection: it suffices to rule out
nonidentity central involutions of P that centralize Y. -/
theorem inf_centralizer_eq_bot_of_central_involutions
    (P Y : Subgroup G) (hP : IsPGroup 2 P)
    (hPY : P ≤ normalizer (Y : Set G))
    (hfixed : ∀ x ∈ P, x ∈ centralizer (P : Set G) →
      x ∈ centralizer (Y : Set G) → x ^ 2 = 1 → x = 1) :
    P ⊓ centralizer (Y : Set G) = ⊥ := by
  apply inf_centralizer_eq_bot_of_omegaCenterIn_inf_eq_bot P Y hP hPY
  apply bot_unique
  rintro x ⟨hx, hy⟩
  obtain ⟨hxP, hxc, hx2⟩ := (mem_omegaCenterIn_iff P x).mp hx
  exact hfixed x hxP hxc hy hx2

end Subgroup
