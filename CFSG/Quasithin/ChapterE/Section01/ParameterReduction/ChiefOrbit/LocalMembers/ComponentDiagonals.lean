module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.ComponentDiagonals.ResidualAction
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.ComponentDiagonals.Sylow
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.ComponentDiagonals.QuotientCover

/-!
# Assembly of the component quotient cover in E.1.11

The residual-action identity and the actual Sylow intersection in K_A are
proved in the imported extensions. Once the diagonal quotient members and
their cover are constructed, E.1.10(7), inheritance, and E.1.10(8) give the
ambient containment below with kernel O∞(K_A).

This theorem remains conditional on `ComponentQuotientCover`. Existence of
that family, including the equivariant diagonal construction and rank bounds,
is the remaining source obligation. The interface is not an unconditional
proof of the component branch of E.1.11.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed p.213.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

/-- The actual quotient-lifting consumer, with its residual-action premise
proved and with the source solvable radical as kernel. Only the quotient
member construction and cover remain explicit. -/
theorem memberOrbitGroup_le_generationTarget_of_component_quotient_cover
    {n : ℕ} (hn : 0 < n) (T : Sylow 2 G) (J : Subgroup G)
    (hcore : pCore 2 G = ⊥) {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    {A : Subgroup G} (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
    {P : Subgroup (localGroup T J)}
    (hc : ECaseComponent ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P)
    (R : Sylow 2 (memberOrbitGroup T J A P))
    (hR : (R : Subgroup (memberOrbitGroup T J A P)) =
      (T : Subgroup G).subgroupOf (memberOrbitGroup T J A P))
    (c : ComponentQuotientCover n T J A P R) :
    memberOrbitGroup T J A P ≤ generationTarget n T Ω := by
  let _ := hΩ.1 A hA
  exact le_generationTarget_of_solvable_quotient_member_cover hn T hΩ hA hAT
    (memberOrbitGroup T J A P) R hR (tau_le_memberOrbitGroup T J A P)
    (solvableRadical (memberOrbitGroup T J A P))
    (memberOrbitGroup_residual_action_of_componentCase T J A hcore hAT hc)
    c.overgroup c.le_orbitGroup c.sylow c.sylow_eq c.tau_le c.member c.isEMemberAt c.cover

end CFSG.Quasithin.ChapterE.ChiefOrbit
