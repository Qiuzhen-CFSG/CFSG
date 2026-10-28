module

public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoReduction
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoElementary
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoComplement

/-!
# Two-primary perfect central covers of J4

The certified elementary-preimage and invariant-complement calculations for
the literal ATLAS max1 subgroup exclude central double covers of `Janko4.Model`.
The prime-kernel reduction in `JankoReduction` then excludes two from every
finite perfect central covering kernel, so a two-group kernel is trivial.

The center-quotient corollary uses the original projection by the entire center;
it requires no bound on the center's order or exponent beyond being a two-group.
This supplies the J4 two-primary case of Aschbacher--Smith I.1.3, printed p.407
of `refs/quasithin.pdf`, whose exhaustive nontrivial-multiplier list omits J4
and refers to GLS98 Section 6.1, Tables 6.1.2--3, and the ATLAS.
-/

public section
open Subgroup PerfectCentralCovering
namespace Janko4.TwoPrimary

variable {E : Type*} [Group E] [Finite E]

/-- Two does not divide the kernel of any finite perfect central cover of the
actual J4 model. -/
theorem kernel_not_two (f : Cover E Model) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker :=
  kernel_not_two_of_local_calculations
    elementaryPreimageCalculation invariantComplementCalculation f

/-- A central two-group kernel of a surjection from a finite perfect group
onto the actual J4 model is trivial. -/
theorem kernel_eq_bot [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (h2 : IsPGroup 2 f.ker) : f.ker = ⊥ :=
  kernel_eq_bot_of_local_calculations
    elementaryPreimageCalculation invariantComplementCalculation f hf hc h2

/-- If a finite perfect group's quotient by its entire center is the actual
J4 model and that center is a two-group, then the center is trivial. -/
theorem center_eq_bot_of_quotient_equiv [Group.IsPerfect E]
    (e : E ⧸ center E ≃* Model) (h2 : IsPGroup 2 (center E)) : center E = ⊥ :=
  center_eq_bot_of_quotient_equiv_of_local_calculations
    elementaryPreimageCalculation invariantComplementCalculation e h2

end Janko4.TwoPrimary
