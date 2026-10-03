module

public import Stellmacher.SectionNine.DistanceOneCoreCollapse
public import Stellmacher.SectionNine.DistanceOneChiefBranchExclusion

/-!
# Initial core equality in the distance-one case

The noncentral chief branch is impossible by the explicit chief-action
contradiction. Therefore the initial residual commutator is contained in the
initial center. The center-free odd-image core collapse then identifies the
initial two-core with that center, giving relation (11) in Stellmacher (9.1).
The ambient and graph groups remain distinct throughout; only the local
context is passed to the collapse theorem.

Source: Stellmacher, Journal of Algebra 190 (1997), pp. 47–48, relations
(9)–(11). The branch exclusion and core-collapse modules provide the proved
source reductions used here.
-/

namespace Stellmacher.SectionNine

open Stellmacher.Later Stellmacher.SectionsFiveToSeven

universe u

/-- The initial two-core equals the initial center in the actual distance-one
configuration after the faithful action calculation. -/
public theorem distance_one_core_eq_center_of_faithful
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext) :
    QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a := by
  apply distance_one_core_eq_center_of_residual_bound ctx.toLocalContext
  apply distance_one_residual_bound_of_chief_branch_exclusion ctx hb hfaith
  intro branch
  exact distance_one_chief_branch_false ctx hb hfaith branch

end Stellmacher.SectionNine
