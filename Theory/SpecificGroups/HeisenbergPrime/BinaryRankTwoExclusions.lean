module
public import Theory.SpecificGroups.HeisenbergPrime.SolvableSylowExclusion
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Cubic
public import Theory.SpecificGroups.SymplecticFour.SylowFixedCubic
public import Theory.SpecificGroups.SymplecticFour.Sylow.NormalizerDerived
public import Theory.SpecificGroups.G2.CubicFieldActors
public import Theory.SpecificGroups.G2.NoncyclicOddActor

/-!
# Rank-two binary Lie models exclude the local Heisenberg action

For Sp₄(q) and G₂(q), q > 2 even, a cubic actor in an automorphism overgroup
of three-rank at most two is inner. A faithful ternary Heisenberg action
inside a solvable odd-index subgroup would therefore lie in a solvable
Sylow-two overgroup of the model. Its Borel quotient is abelian, which
contradicts the nonabelian Heisenberg subgroup.

Source: the characteristic-two catalogue exclusion in Aschbacher–Smith
14.7.26, printed p.1053 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace HeisenbergPrime.BinaryRankTwoExclusions
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The symplectic rank-two model cannot support the specified local action. -/
theorem symplectic {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n) (hq : 2 < Nat.card F)
    (A : Subgroup (MulAut (Sp F))) (hA : MulAut.innerSubgroup (Sp F) ≤ A)
    (hr : primeRank 3 A ≤ 2) (J : Subgroup A) [Group.IsSolvable J] (ho : Odd J.index)
    (f : HeisenbergPrime 3 →* A) (hf : Function.Injective f) (hJ : ∀ y, f y ∈ J) : False := by
  apply HeisenbergPrime.no_inner_action_in_solvable_odd_index EvenProjective.center_eq_bot
    (fun S N hs hSN => solvable_sylow_overgroup_normalizes hq S N hs hSN)
    (commutator_sylow_normalizer_le hF hn) A hA J ho f hf hJ
  intro y
  apply OddFieldActors.cubic_primePower_actor_inner hq A hA hr (f y) (f y).property
  refine ⟨1,?_⟩
  change (A.subtype.comp f) y ^ 3 = 1
  rw [←map_pow,HeisenbergPrime.pow_prime (by decide : 3 ≠ 2),map_one]

/-- The G₂ model cannot support the specified local action. -/
theorem g2 (hq : 2 < Nat.card F)
    (A : Subgroup (MulAut (Atlas.G2.Model F))) (hA : MulAut.innerSubgroup (Atlas.G2.Model F) ≤ A)
    (hr : primeRank 3 A ≤ 2) (J : Subgroup A) [Group.IsSolvable J] (ho : Odd J.index)
    (f : HeisenbergPrime 3 →* A) (hf : Function.Injective f) (hJ : ∀ y, f y ∈ J) : False := by
  apply HeisenbergPrime.no_inner_action_in_solvable_odd_index
    (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hq)
    (fun S N hs hSN => Atlas.G2.solvable_sylow_overgroup_normalizes hq S N hSN hs)
    Atlas.G2.NoncyclicOddActor.commutator_sylow_normalizer_le A hA J ho f hf hJ
  intro y
  apply Atlas.G2.CubicFieldActors.cubic_primePower_actor_inner hq A hA hr (f y) (f y).property
  refine ⟨1,?_⟩
  change (A.subtype.comp f) y ^ 3 = 1
  rw [←map_pow,HeisenbergPrime.pow_prime (by decide : 3 ≠ 2),map_one]
end HeisenbergPrime.BinaryRankTwoExclusions
