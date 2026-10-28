module

public import Stellmacher.SectionEight.GeneratedContext

public import Stellmacher.SectionEight.EightTwoDistanceOneCoreAction
public import Stellmacher.SectionOne.ElementaryDihedralCoreFourFactor

/-!
# Normal central four-factors at critical distance one

For the exact Section Eight context, assume the first-step vertex center
is noncentral, the critical distance is one, and both distinguished
stabilizers have elementary abelian two-cores. Each of these cores is the
direct product of a normal subgroup of order four and its stabilizer's
center, with all factors native subgroups of that stabilizer.

The direct distinguished-edge core-action theorem supplies fixed-core
index two under an actual Sylow two-subgroup at either end. The local
quotient theorem supplies the actual odd-dihedral core quotient, while
the edge characteristic data give self-centralization of the core.
The full-core decomposition theorem then applies (1.7) to the faithful
action on the entire core: its single nontrivial support has order four
and is the commutator factor, complementary to the global fixed subgroup,
which is the stabilizer center.

Source: Stellmacher (8.2), final paragraph, Journal of Algebra 190 (1997),
p.38, `refs/latex/stellmacher-n-group.tex`. The source uses a backward edge;
the direct distinguished-edge action argument avoids any transfer from
that edge. The decomposition is proved on the whole core, not inferred
from a decomposition of the vertex center. No whole-group classification,
center-order bound, or identification of the faithful vertex-center
quotient with the actual core quotient is assumed.

The supplemental theorem uses `SectionEightLocalContext` and its genuine
Section Seven hypotheses. The original public theorem remains a wrapper
through `SectionEightContext.toLocalContext`, preserving the graph and
critical path definitionally. No additional Sylow hypothesis is imposed
on the ambient group of the supplemental theorem.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven
universe u

public theorem eight_two_distance_one_four_factor_local
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
          U ⊓ Subgroup.center (GAt ctx.Γ d) = ⊥ ∧ Nat.card U = 4 := by
  have h7 := ctx.sectionSeven
  have hcharacteristic := SevenSix.edge_characteristic_data h7 ctx.Γ ctx.criticalPath
  have hquot := eight_two_dihedral_core_local ctx hcenter
  have haction := eight_two_distance_one_core_action_local ctx hcenter hlength helementary
  intro d hd
  let _ := helementary d hd
  obtain ⟨T, hT⟩ := haction d hd
  apply SectionOne.elementary_dihedral_core_four_factor ?_ (hquot d) T hT
  rcases hd with rfl | rfl
  · exact hcharacteristic.1
  · exact hcharacteristic.2

public theorem eight_two_distance_one_four_factor
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
          U ⊓ Subgroup.center (GAt ctx.Γ d) = ⊥ ∧ Nat.card U = 4 :=
  eight_two_distance_one_four_factor_local ctx.toLocalContext hcenter hlength helementary

end Stellmacher.SectionEight
