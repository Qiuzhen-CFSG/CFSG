module
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Counting elementary subgroups with a noncommuting cover

A square-one cover whose parts have no distinct commuting elements injects
each elementary abelian subgroup into its set of parts. The concrete M₁₂ and
M₂₄ applications use the existing native Sylow enumerations.

Source application: Aschbacher--Smith, G.7.3(2), printed p.348.
-/

public section
namespace Sporadic.Mathieu.SmallModuleRanks

/-- A commuting subgroup uses at most one element from each part of a cover
whose distinct elements do not commute. Only square-one elements need coverage. -/
theorem elementary_card_le_of_commuting_cover {G : Type*} [Group G] [Finite G]
    {n m : ℕ} (b : Fin n → Fin m → G)
    (hcover : ∀ g : G, g ^ 2 = 1 → ∃ c a, b c a = g)
    (huniq : ∀ c a a', b c a * b c a' = b c a' * b c a → b c a = b c a')
    (E : Subgroup G) (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ n := by
  classical
  have hex (g : E) : ∃ c a, b c a = g.val :=
    hcover g.val (congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p g))
  let f : E → Fin n := fun g => (hex g).choose
  have hf : Function.Injective f := by
    intro g h he
    obtain ⟨a, ha⟩ := (hex g).choose_spec
    obtain ⟨a', ha'⟩ := (hex h).choose_spec
    change b (f g) a = g.val at ha
    change b (f h) a' = h.val at ha'
    rw [← he] at ha'
    apply Subtype.ext
    rw [← ha, ← ha']
    apply huniq
    rw [ha, ha']
    exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm g h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

end Sporadic.Mathieu.SmallModuleRanks
