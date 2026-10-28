module

public import Mathlib.GroupTheory.Sylow

/-!
# Bounding a normalizing p-subgroup through its action

For a finite p-subgroup P normalizing L, conjugation has kernel C_P(L)
and p-group image in Aut(L). Containing that image in an actual Sylow
subgroup A gives |P| ≤ |A||C_P(L)|. No faithfulness assumption or assertion
that P is Sylow in the ambient group is needed.

Source: the first order comparison in Aschbacher–Smith, combined manuscript
of 1 March 2004, proof of 16.3.4, printed p.1178.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The order of a normalizing p-subgroup is bounded by its centralizer
order times the order of a Sylow p-subgroup of the full automorphism group. -/
public theorem exists_sylow_aut_card_bound
    {p : ℕ} [Fact p.Prime] (P L : Subgroup G) (hp : IsPGroup p P)
    (hn : P ≤ normalizer (L : Set G)) :
    ∃ A : Sylow p (MulAut L),
      Nat.card P ≤ Nat.card A * Nat.card (P ⊓ centralizer (L : Set G) : Subgroup G) := by
  let f := L.normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hk : f.ker = (P ⊓ centralizer (L : Set G)).subgroupOf P := by
    ext x
    constructor
    · intro hx
      have hx' : (⟨x, hn x.property⟩ : normalizer (L : Set G)) ∈
          L.normalizerMonoidHom.ker := hx
      rw [normalizerMonoidHom_ker] at hx'
      exact ⟨x.property, hx'⟩
    · intro hx
      have hx' : (⟨x, hn x.property⟩ : normalizer (L : Set G)) ∈
          L.normalizerMonoidHom.ker := by
        rw [normalizerMonoidHom_ker]
        exact hx.2
      exact hx'
  have hkc : Nat.card f.ker = Nat.card (P ⊓ centralizer (L : Set G) : Subgroup G) := by
    rw [hk]
    exact Nat.card_congr (subgroupOfEquivOfLe
      (show (P ⊓ centralizer (L : Set G)) ≤ P from inf_le_left)).toEquiv
  have hr : IsPGroup p f.range :=
    hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨A, hA⟩ := hr.exists_le_sylow
  refine ⟨A, ?_⟩
  calc
    Nat.card P = Nat.card f.range * Nat.card (P ⊓ centralizer (L : Set G) : Subgroup G) := by
      rw [← hkc, ← index_ker, index_mul_card]
    _ ≤ Nat.card A * Nat.card (P ⊓ centralizer (L : Set G) : Subgroup G) :=
      Nat.mul_le_mul_right _ (card_le_of_le hA)

end Subgroup
