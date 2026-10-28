module

public import Stellmacher.SectionEight.GeneratedContext

public import Stellmacher.SectionEight.EightTwoDistanceOneFourFactor
public import Stellmacher.SectionEight.EightTwoDistanceOneCenterBound

/-!
# The distance-one core structure in Stellmacher (8.2)

For the noncentral Section Eight context at critical distance one, assume
explicitly that both distinguished native two-cores are elementary abelian.
Each core is the direct product of a normal subgroup of order four and the
stabilizer center, the center has order at most two, and the actual quotient
by the two-core is S3. These are the structural inputs to the terminal
whole-stabilizer classifier; that classification is not used here.

The four-factor theorem works directly on the distinguished edge. Its
rank-one Sylow action on the whole core and the (1.7) decomposition produce
one order-four commutator support with central complement, avoiding the
source's backward-edge transfer. The quotient bridge acts on the three
nonidentity support elements and proves its kernel equals the actual core.
The center-bound theorem places both stabilizer centers in the common
Sylow center, proves their intersection trivial using generation and the
ambient trivial two-core, and compares their orders with the proper
Sylow-center subgroup of each core. This module assembles those results
without identifying the vertex-center action kernel with the core.

Source: Stellmacher (8.2), final paragraph, Journal of Algebra 190 (1997),
printed p.38, `refs/latex/stellmacher-n-group.tex`.

The supplemental theorem uses `SectionEightLocalContext` and its genuine
Section Seven hypotheses. The original public theorem remains a wrapper
through `SectionEightContext.toLocalContext`, preserving the graph and
critical path definitionally. No additional Sylow hypothesis is imposed
on the ambient group of the supplemental theorem.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

public theorem eight_two_distance_one_core_structure_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 1)
    (helementary : ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        IsElementaryAbelian 2 (pCore 2 (GAt ctx.Γ d))) :
    ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        ∃ U : Subgroup (GAt ctx.Γ d), U.Normal ∧
          pCore 2 (GAt ctx.Γ d) = U ⊔ Subgroup.center (GAt ctx.Γ d) ∧
          U ⊓ Subgroup.center (GAt ctx.Γ d) = ⊥ ∧
          Nat.card U = 4 ∧ Nat.card (Subgroup.center (GAt ctx.Γ d)) ≤ 2 ∧
          Nonempty ((GAt ctx.Γ d ⧸ pCore 2 (GAt ctx.Γ d)) ≃*
            Equiv.Perm (Fin 3)) := by
  have hfour := eight_two_distance_one_four_factor_local ctx hcenter hlength helementary
  have hbound := eight_two_distance_one_center_bound_local ctx hcenter hlength helementary hfour
  intro d hd
  let _ := helementary d hd
  obtain ⟨U, hnormal, hQ, hintersection, hcard⟩ := hfour d hd
  let _ := hnormal
  exact ⟨U, hnormal, hQ, hintersection, hcard, hbound d hd,
    eight_two_actual_core_quotient_of_four_factor_local ctx hcenter d hd U hQ hcard⟩

public theorem eight_two_distance_one_core_structure
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 1)
    (helementary : ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        IsElementaryAbelian 2 (pCore 2 (GAt ctx.Γ d))) :
    ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        ∃ U : Subgroup (GAt ctx.Γ d), U.Normal ∧
          pCore 2 (GAt ctx.Γ d) = U ⊔ Subgroup.center (GAt ctx.Γ d) ∧
          U ⊓ Subgroup.center (GAt ctx.Γ d) = ⊥ ∧
          Nat.card U = 4 ∧ Nat.card (Subgroup.center (GAt ctx.Γ d)) ≤ 2 ∧
          Nonempty ((GAt ctx.Γ d ⧸ pCore 2 (GAt ctx.Γ d)) ≃*
            Equiv.Perm (Fin 3)) :=
  eight_two_distance_one_core_structure_local ctx.toLocalContext hcenter hlength helementary

end Stellmacher.SectionEight
