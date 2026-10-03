module
public import Stellmacher.SectionNine.NineTenFiveExcludedCenter
public import Stellmacher.SectionNine.NineTenContainedCenterContradiction
/-!
# The normalized distance-five configuration is impossible

Retain both geometric extraction packets on the same normalized critical
path. At length five, the excluded-center branch forces the terminal center
into the source residual-neighborhood layer. The contained-center branch
contradicts precisely that inclusion. This thin assembly preserves every
original actor, coatom, residual subgroup, and extraction witness.

The two imported proofs supply the final paragraphs of Stellmacher (9.10),
printed p.59. Together with the proved long-distance bound, this is the
remaining obstruction needed for the original and ambient classification
statements in LemmaNineTen.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_five_contradiction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 5)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hactorNeighbor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorComm : twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆)
    (hnew : ctx.Γ.act data.x⁻¹ second = ctx.criticalPath.a)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcenters : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (firstActor : G) (firstE firstA0 : Subgroup G)
    (firstData : NineThreeGeometricData ctx.Γ ctx.criticalPath.a'
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
      (VAt ctx.Γ ctx.criticalPath.firstStep) firstE firstA0 firstActor)
    (hfirstNew : ctx.Γ.act firstData.x⁻¹
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) =
        neighbor)
    (hfirstActors : ∀ b : G, b ∈ VAt ctx.Γ ctx.criticalPath.firstStep → b ∉ firstA0 →
      twoResidualIn firstE ≤ ⁅twoResidualIn firstE, Subgroup.zpowers b⁆) :
    False := by
  exact nine_ten_five_contradiction_of_terminal_center_le ctx hb hterminalNot hfirstNot
    neighbor second actor E A0 data hsecond hactorNeighbor hactorComm hnew hneighbor hcenters
      firstActor firstE firstA0 firstData hfirstNew hfirstActors
    (nine_ten_five_terminal_center_le_residual_neighborhood ctx hb hterminalNot hfirstNot
    neighbor second actor E A0 data hsecond hactorNeighbor hactorComm hnew hneighbor hcenters
      firstActor firstE firstA0 firstData hfirstNew hfirstActors)

end Stellmacher.SectionNine
