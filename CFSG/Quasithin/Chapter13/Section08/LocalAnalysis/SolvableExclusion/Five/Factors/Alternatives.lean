module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.FactorData
public import Mathlib.Tactic

/-!
# The intermediate order-four actor and its geometric equality case

These are construction targets for two independent steps of 13.8.13.
`RankTwoFactors` retains the actual five-factors, their two involution
actors inside H*, the moved planes, and both the moved order and fixed
index on the whole quotient. The fixed index is needed to check the
equality hypothesis of F.9.16(2); the moved order alone does not check it.

`CommonCenterOnDH` describes the equality conclusion on the literal image
of D_H in UH/V₁. Its faithfulness condition says precisely that an element
of Uγ* fixing that image pointwise is the identity. Neither record asserts
existence. The source application must construct both before invoking the
common-center contradiction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, and F.9.16(2), printed pp.323–324.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Subgroup
variable {G : Type*} [Group G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]

/-- The second alternative before the rank-two actor is excluded. -/
structure RankTwoFactors (a : StarAction H UH V₁) (P Uγ : Subgroup G) where
  factors : Factorization a P
  count_eq_two : factors.count = 2
  actor_card : Nat.card (Source.starImage H Uγ) = 4
  first : Subgroup (Source.Hstar H)
  second : Subgroup (Source.Hstar H)
  first_card : Nat.card first = 2
  second_card : Nat.card second = 2
  generated : Source.starImage H Uγ = first ⊔ second
  commute : ⁅first, second⁆ = ⊥
  disjoint : Disjoint first second
  first_moves : ⁅first, Source.starImage H
    (factors.factor ⟨0, factors.count_pos⟩)⁆ ≠ ⊥
  second_moves : ⁅second, Source.starImage H
    (factors.factor ⟨1, by omega⟩)⁆ ≠ ⊥
  first_fixes : ⁅first, Source.starImage H
    (factors.factor ⟨1, by omega⟩)⁆ = ⊥
  second_fixes : ⁅second, Source.starImage H
    (factors.factor ⟨0, factors.count_pos⟩)⁆ = ⊥
  first_plane : Nat.card
    (commutatorAction (first.map a.action) (UH ⧸ V₁.subgroupOf UH)) = 4
  second_plane : Nat.card
    (commutatorAction (second.map a.action) (UH ⧸ V₁.subgroupOf UH)) = 4
  moved_card : Nat.card
    (commutatorAction (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)) = 16
  fixed_index : (FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)).index = 16

/-- The precise common-center consequences consumed in the order-four case. -/
structure CommonCenterOnDH (a : StarAction H UH V₁) (Uγ A₁ : Subgroup G) : Prop where
  index : (Source.DH UH Uγ A₁).relIndex UH = 4
  invariant : ∀ b : a.actors Uγ,
    ∀ d ∈ tildeImage UH V₁ (Source.DH UH Uγ A₁),
      b • d ∈ tildeImage UH V₁ (Source.DH UH Uγ A₁)
  faithful : ∀ b ∈ Source.starImage H Uγ,
    (∀ d ∈ tildeImage UH V₁ (Source.DH UH Uγ A₁), a.action b d = d) → b = 1
  center_card : Nat.card (tildeImage UH V₁ A₁) = 2
  center_le : tildeImage UH V₁ A₁ ≤ tildeImage UH V₁ (Source.DH UH Uγ A₁)
  displacement_le : commutatorSubgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)
    (tildeImage UH V₁ (Source.DH UH Uγ A₁)) ≤ tildeImage UH V₁ A₁

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
