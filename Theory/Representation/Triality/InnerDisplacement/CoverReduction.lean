module

public import Theory.Representation.CharacteristicTwoIrreducibleRank
public import Theory.Representation.GroupEquivalence

/-!
# Eliminating central two-subgroups in faithful irreducible actions

An irreducibly acting group's central involutions are trivial in
characteristic two. Induction on the exponent of a central two-element
then kills every element of a central two-group. Thus a faithful irreducible
action forces the center to vanish once it is known to be a two-group.
Neither absolute irreducibility nor finiteness of the coefficient field is
needed for this step.

This is the defining-characteristic cover reduction preceding
Guralnick--Malle, *Classification of 2F-modules, II*, §8 (internal p.53).
For the triality application the prime-to-two multiplier calculation still
has to supply the two-group hypothesis.
-/

public section

namespace Triality.InnerDisplacement
open Representation
variable {E G W : Type*} [Field E] [CharP E 2] [Group G]
  [AddCommGroup W] [Module E W]
  (τ : Representation E G W) [τ.IsIrreducible]

/-- The prime-to-two cover calculation suffices for every faithful
irreducible characteristic-two action. -/
theorem center_eq_bot_of_twoGroup (hf : Function.Injective τ)
    (hc : IsPGroup 2 (Subgroup.center G)) : Subgroup.center G = ⊥ := by
  let : IsIrreducible (τ.comp (⊤ : Subgroup G).subtype) :=
    (irreducible_comp_surjective_iff _ (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩) τ).mpr
      inferInstance
  have hkill (k : ℕ) : ∀ z : G, z ∈ Subgroup.center G → z ^ 2 ^ k = 1 → z = 1 := by
    induction k with
    | zero => intro z _ hz; simpa using hz
    | succ k ih =>
      intro z hz he
      apply ih z hz
      apply CharacteristicTwoIrreducible.centralizing_square_one_eq_one τ ⊤ hf
      · simpa only [pow_succ, pow_mul] using he
      · exact Subgroup.mem_centralizer_iff.mpr
          (fun g _ => Subgroup.mem_center_iff.mp (pow_mem hz (2 ^ k)) g)
  apply le_bot_iff.mp
  intro z hz
  obtain ⟨k, hk⟩ := hc.exists_pow_pow_eq_one (⟨z, hz⟩ : Subgroup.center G)
  exact Subgroup.mem_bot.mpr (hkill k z hz (congrArg Subtype.val hk))
end Triality.InnerDisplacement
