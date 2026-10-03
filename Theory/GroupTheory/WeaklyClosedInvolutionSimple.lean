module

public import Theory.GroupTheory.ZStar.CoreFree
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Weakly closed involutions in finite simple groups

An involution central in a Sylow two-subgroup and weakly closed there is
central in the ambient finite simple group. Simplicity makes the odd core
trivial: otherwise it is the whole group, contradicting the presence of an
element of order two. Glauberman's core-free Z-star theorem then applies.

Source: G. Glauberman, “Central elements in core-free groups”,
J. Algebra 4 (1966).
-/

open Subgroup

/-- A central Sylow involution that is weakly closed in a finite simple group
is central in the whole group. -/
public theorem Sylow.weakly_closed_involution_mem_center_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (z : S) (hz : orderOf z = 2)
    (hzC : z ∈ center S)
    (hweak : ∀ t : S, IsConj (z : G) (t : G) → t = z) :
    (z : G) ∈ center G := by
  have hzG : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hz
  have hcore : pPrimeCore 2 G = ⊥ := by
    rcases (pPrimeCore_normal (p := 2) (G := G)).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hc := pPrimeCore_coprime_card (p := 2) (G := G)
      rw [ht, Subgroup.card_top] at hc
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hc
        (hzG ▸ orderOf_dvd_natCard (z : G))).elim
  have hz1 : (z : G) ≠ 1 := by
    intro h
    simp [h] at hzG
  have hz2 : (z : G) ^ 2 = 1 := by
    simpa only [hzG] using pow_orderOf_eq_one (z : G)
  refine Glauberman.ZStar.glauberman_zstar_corefree hcore S (z : G)
    ⟨hz1, hz2⟩ z.property ?_ ?_
  · intro s hs
    exact congrArg Subtype.val (mem_center_iff.mp hzC ⟨s, hs⟩)
  · refine ⟨z.property, ?_⟩
    intro g hg
    exact congrArg Subtype.val (hweak ⟨g * z * g⁻¹, hg⟩ (isConj_iff.mpr ⟨g, rfl⟩))
