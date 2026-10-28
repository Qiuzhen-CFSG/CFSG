module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredIntersection

/-!
# The original central cubic residual without a natural-subgroup assumption

The image of L₀ = O²(O₂,Z(L)) in L/O₂(L) is its order-three center.
Relative normality identifies L₀/O₂(L₀) with that center. Thus L₀ is
nontrivial, and the original local uniqueness theorem gives N_G(L₀)=N_G(L).
In particular L₀ cannot be normal in an escaping overgroup of T.

These are the central-residual clauses used in the covered 13.3.9 argument.
They use the genuine covered quotient and preserve the original module;
no four-dimensional NaturalSetup is required.

Source: Aschbacher--Smith Notation 13.2.1 and 13.2.2(9), pp.877--878;
the proof of 13.3.9, p.887.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02
open Section08
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual central cubic residual is nontrivial. -/
theorem covered_zero_ne_bot
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3) : zero L ≠ ⊥ := by
  intro he
  have hh := Solvable.covered_zero_core_card hc
  rw [he] at hh
  have h1 : Nat.card ((⊥ : Subgroup G) ⧸ pCore 2 (⊥ : Subgroup G)) = 1 := Nat.card_unique
  omega

/-- Source 13.2.2(9) for L₀, retaining the original T and covering center. -/
theorem covered_zero_normalizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    normalizer (zero L : Set G) = normalizer (L : Set G) := by
  apply le_antisymm _ (normalizer_le_zero_normalizer L)
  exact h.normal_subgroup_normalizer_le hTL ((zero_le L).trans le_sup_left)
    (covered_zero_ne_bot hc)
    ((sup_le L.le_normalizer hTL).trans (normalizer_le_zero_normalizer L))

/-- The literal L₀ alternative in 13.3.9 is excluded by the original outside
overgroup, without identifying either of the other covered residuals. -/
theorem covered_zero_not_normal_outside
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    {H : Subgroup G} (hout : ¬ H ≤ normalizer (L : Set G)) :
    ¬ H ≤ normalizer (zero L : Set G) := by
  rwa [covered_zero_normalizer h hTL hc]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
