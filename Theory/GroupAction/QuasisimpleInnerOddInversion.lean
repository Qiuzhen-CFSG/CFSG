module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore

/-!
# Inner automorphisms inverting the odd core of a quasisimple group

The odd core of a quasisimple group is central or the whole group. In the
central case an inner automorphism both fixes and inverts it, so odd order
forces it to be trivial. In the whole-group case the same argument first
kills the conjugating element, then the whole core. The center therefore
is exactly the two-core. No Schur multiplier calculation is used.

Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.502.
-/

public section
namespace MulAut

open Subgroup Theory.GroupTheory

/-- Source odd-core inversion and innerness force a purely two-primary center. -/
theorem center_eq_twoCore_of_inner_inverts_oddCore {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (a : MulAut G) (hi : a ∈ (MulAut.conj (G := G)).range)
    (hinv : ∀ x ∈ pPrimeCore 2 G, a x = x⁻¹) :
    center G = pCore 2 G := by
  obtain ⟨g, rfl⟩ := hi
  have fixed_trivial (x : pPrimeCore 2 G) (hfix : MulAut.conj g (x : G) = x) :
      (x : G) = 1 := by
    have he : (x : G) = (x : G)⁻¹ := hfix.symm.trans (hinv x x.property)
    have hp : x ^ 2 = 1 := by
      apply Subtype.ext
      change (x : G) ^ 2 = 1
      rw [pow_two]
      exact (congrArg (fun z : G => z * x) he).trans (inv_mul_cancel (x : G))
    have hc := (pPrimeCore_coprime_card (p := 2) (G := G)).symm
    have hx : x = 1 := hc.pow_left_bijective.injective (by simpa using hp)
    exact congrArg Subtype.val hx
  apply IsQuasisimple.center_eq_pCore
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  rcases IsQuasisimple.normal_le_center_or_eq_top (pPrimeCore 2 G) with hc | ht
  · apply fixed_trivial ⟨x, hx⟩
    change g * x * g⁻¹ = x
    rw [mem_center_iff.mp (hc hx) g]
    group
  · have hg : g = 1 := fixed_trivial ⟨g, ht ▸ mem_top g⟩ (by simp)
    apply fixed_trivial ⟨x, hx⟩
    simp [hg]

end MulAut
