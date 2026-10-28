module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor.Binary
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor.LocalReduction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor.Nonbinary
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor.Transport

/-!
# Assembly of the second G₂ parabolic actor argument

Every subnormal two-perfect subgroup of the second parabolic inside the
derived G₂ model is trivial if its commutators with the intrinsic two-core
have square one. Above field order two, perfectness identifies this parabolic
with the full parabolic, where the torus and long-local calculations apply.
At field order two, coefficientwise field transport identifies it with the
actual second parabolic of G₂(2)′, where the binary calculation applies.
Both calculations retain arbitrary radical perturbations of the actors.

The final theorem discharges both standard-model premises of the transport
reduction. It supplies the second-coordinate actor rigidity needed for the
relative-block exclusion in Aschbacher–Smith 2.3.9(7), printed p.526.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped commutatorElement

/-- Field transport reduces the exact derived-parabolic statement to the full
nonbinary parabolic and the standard binary derived parabolic. -/
theorem second_actor_eq_bot_of_standard_cases
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hlarge : 2 < Nat.card F → ∀ X : Subgroup (parabolic₂ (F := F)),
      X.IsSubnormal → IsPPerfect 2 X →
      (∀ q ∈ pCore 2 (parabolic₂ (F := F)), ∀ x ∈ X,
        (⁅q,x⁆ : parabolic₂)^2 = 1) → X = ⊥)
    (hbinary : ∀ X : Subgroup BinaryParabolicPair.derivedSecond,
      X.IsSubnormal → IsPPerfect 2 X →
      (∀ q ∈ pCore 2 BinaryParabolicPair.derivedSecond, ∀ x ∈ X,
        (⁅q,x⁆ : BinaryParabolicPair.derivedSecond)^2 = 1) → X = ⊥)
    (X : Subgroup (secondModel F)) (hX : X.IsSubnormal) (hp : IsPPerfect 2 X)
    (hsq : ∀ q ∈ pCore 2 (secondModel F), ∀ x ∈ X,
      (⁅q,x⁆ : secondModel F)^2 = 1) : X = ⊥ := by
  by_cases hq : 2 < Nat.card F
  · exact SecondActor.eq_bot_of_equiv (SecondActor.secondModelFullEquiv hq)
      (hlarge hq) X hX hp hsq
  · have htwo : Nat.card F = 2 := by
      have := Finite.one_lt_card (α := F)
      omega
    exact SecondActor.eq_bot_of_equiv (SecondActor.secondModelBinaryEquiv htwo)
      hbinary X hX hp hsq

/-- A subnormal two-perfect subgroup of the actual second derived G₂
parabolic acting with square-one commutators on its intrinsic two-core is
trivial, over every finite field of characteristic two. -/
theorem second_actor_eq_bot
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (X : Subgroup (secondModel F)) (hX : X.IsSubnormal) (hp : IsPPerfect 2 X)
    (hsq : ∀ q ∈ pCore 2 (secondModel F), ∀ x ∈ X,
      (⁅q,x⁆ : secondModel F)^2 = 1) : X = ⊥ := by
  exact second_actor_eq_bot_of_standard_cases SecondActor.full_actor_eq_bot
    SecondActor.binary_actor_eq_bot X hX hp hsq

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks

end
