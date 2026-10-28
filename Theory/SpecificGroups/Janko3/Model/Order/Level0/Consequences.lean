module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0Data
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Consequences of the first J3 Schreier transitions

The transition identities decompose every word into a transversal representative
and an element of H1. Distinct representative images give index 6156. A word
fixing zero must use the identity representative, so H1 is exactly the point
stabilizer in H0. The final certificate supplies the explicit transition premise.
Source: the Schreier decomposition in `Theory/GroupTheory/WordSubgroup.lean`,
with the ATLAS J3G1-p6156B0 witnesses from `Order/data/`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0
open Theory.GroupTheory

/-- The exact transition contract for the supplied transversal and factor words. -/
public abbrev Steps : Prop := ∀ (i : Fin 4) (r : Fin 6156),
  L0Gen i * L0Rep r = L0Rep (L0Act i r) * evalWord L1Gen (L0Factor i r)

public theorem card_step (h : Steps) : Nat.card H0 = 6156 * Nat.card H1 :=
  wordSubgroup_card_eq_mul_next
    L0Gen L0Inv L0Inv_spec L1Gen L1Inv L1Inv_spec
    L0Rep L0Act L0Factor (0 : Fin 6156) L0Point (0 : Fin 6156)
    L0Rep_mem H1_le L0Rep_base L0Rep_point L0Point_injective H1_fix h

public theorem decompose (h : Steps) (g : H0) :
    ∃ (r : Fin 6156) (k : H1), (g : Equiv.Perm (Fin 6156)) = L0Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ (r : Fin 6156) (k : H1), evalWord L0Gen w = L0Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil =>
    exact ⟨0, 1, by simp only [evalWord, Subgroup.coe_one, L0Rep_base, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    let f : H1 := ⟨evalWord L1Gen (L0Factor i r),
      evalWord_mem_wordSubgroup L1Gen L1Inv L1Inv_spec _⟩
    refine ⟨L0Act i r, f * k, ?_⟩
    change L0Gen i * evalWord L0Gen w = L0Rep (L0Act i r) *
      (evalWord L1Gen (L0Factor i r) * (k : Equiv.Perm (Fin 6156)))
    rw [hk, ← mul_assoc, h, mul_assoc]

public theorem stabilizer_eq (h : Steps) :
    H1 = H0 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (0 : Fin 6156) := by
  apply le_antisymm
  · intro g hg
    exact ⟨H1_le hg, H1_fix ⟨g, hg⟩⟩
  · intro g hg
    obtain ⟨r, k, hk⟩ := decompose h ⟨g, hg.1⟩
    have hfix : g 0 = 0 := hg.2
    have hp0 : L0Point 0 = 0 := by rw [← L0Rep_point, L0Rep_base]; rfl
    have hp : L0Point r = L0Point 0 := by
      have he := congrArg (fun p : Equiv.Perm (Fin 6156) => p 0) hk
      simpa only [Equiv.Perm.mul_apply, H1_fix, L0Rep_point, hfix, hp0] using he.symm
    have hr := L0Point_injective hp
    rw [hr, L0Rep_base, one_mul] at hk
    change g = (k : Equiv.Perm (Fin 6156)) at hk
    rw [hk]
    exact k.property

end Sporadic.Janko3.OrderCertificate.Level0
