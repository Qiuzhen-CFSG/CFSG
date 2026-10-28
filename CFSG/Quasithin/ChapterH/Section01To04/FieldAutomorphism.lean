module

public import Theory.Representation.FiniteFieldSemilinearDisplacement
public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.Beta.Basic

/-!
# H.0.1 and its field-actor application in H.7

The finite-field descent theorem supplies H.0.1's exact dimension formula and
lower bound for the original binary representation. It also discharges
`FieldAutomorphismFormula` for the literal paired action `Setup.action`, yielding
the H.7 field-actor bounds and exclusion without an extra H.0.1 premise.

Source: Aschbacher–Smith, H.0.1 on printed p.377 and H.7 on pp.388–389,
combined manuscript of 1 March 2004.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section01To04
open Representation.BinaryOffender
variable {F M V : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [Group M]
  [AddCommGroup V] [Module F V] [Module (ZMod 2) V] [FiniteDimensional F V]

/-- H.0.1: the exact displacement formula and its two-thirds lower bound. -/
theorem field_automorphism_displacement (ρ : Representation (ZMod 2) M V)
    {n d p : ℕ} (hF : Nat.card F = 2 ^ n) (hV : Module.finrank F V = d)
    (hp : p.Prime) (ho : Odd p) (x : M) (hx : orderOf x = p)
    (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hsemi : ∀ (a : F) (v : V), ρ x (a • v) = σ a • ρ x v) :
    p * fixedCodim ρ (Subgroup.zpowers x) = (p - 1) * n * d ∧
      2 * n * d ≤ 3 * fixedCodim ρ (Subgroup.zpowers x) := by
  have hn := SymplecticConjugatePair.coefficient_finrank hF
  constructor
  · simpa only [hn, hV] using
      Representation.FiniteFieldSemilinearDisplacement.fixedCodim_formula ρ hp.pos x hx σ hσ hsemi
  · simpa only [hn, hV] using
      Representation.FiniteFieldSemilinearDisplacement.two_thirds_le_fixedCodim
        ρ hp ho x hx σ hσ hsemi
end CFSG.Quasithin.ChapterH.Section01To04

namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open Representation.BinaryOffender
variable {F M V : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [Group M]
  [AddCommGroup V] [Module F V] [Module (ZMod 2) V] [FiniteDimensional F V]

/-- Discharge the actual H.0.1 premise used in the H.7 field-actor step. -/
theorem fieldAutomorphismFormula (ρ : Representation (ZMod 2) M V) :
    FieldAutomorphismFormula (F := F) ρ := by
  intro p x hp _ hx σ hσ hsemi
  exact Representation.FiniteFieldSemilinearDisplacement.fixedCodim_formula ρ hp.pos x hx σ hσ hsemi

/-- The H.7 paired action satisfies H.0.1 without an additional descent premise. -/
theorem Setup.fieldAutomorphismFormula (s : Setup F M) :
    FieldAutomorphismFormula (F := F) s.action :=
  CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.fieldAutomorphismFormula s.action

/-- Apply the proved formula to the literal eight-dimensional paired action. -/
theorem Setup.fieldActor_bounds_unconditional (s : Setup F M) {n : ℕ}
    (hF : Nat.card F = 2^n) {p : ℕ} {x : M} (hp : p.Prime) (ho : Odd p)
    (hx : orderOf x = p) (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hsemi : ∀ (a : F) (v : SymplecticConjugatePair.Space F),
      s.action x (a • v) = σ a • s.action x v) :
    4*n ≤ fixedCodim s.action (Subgroup.zpowers x) ∧
      (n = 1 → 6 ≤ fixedCodim s.action (Subgroup.zpowers x)) :=
  s.fieldActor_bounds hF s.fieldAutomorphismFormula hp ho hx σ hσ hsemi

/-- Exclude semilinear field actors from H.7's small-displacement case. -/
theorem Setup.not_fieldActor_of_small_fixedCodim_unconditional (s : Setup F M) {n : ℕ}
    (hF : Nat.card F = 2^n) {p : ℕ} {x : M} (hp : p.Prime) (ho : Odd p)
    (hx : orderOf x = p) (hsmall : fixedCodim s.action (Subgroup.zpowers x) < 4*n)
    (σ : F ≃+* F) (hσ : orderOf σ = p) :
    ¬ ∀ (a : F) (v : SymplecticConjugatePair.Space F),
      s.action x (a • v) = σ a • s.action x v :=
  s.not_fieldActor_of_small_fixedCodim hF s.fieldAutomorphismFormula hp ho hx hsmall σ hσ
end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
