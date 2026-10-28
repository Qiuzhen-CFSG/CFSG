module

public import Stellmacher.SectionNine.NineFourReduction
public import Stellmacher.SectionNine.NineInitialEdgeCoreProduct
public import Stellmacher.SectionNine.CubicTwoNeighborKernel

/-!
# The normalized actor closure lies in both cores

In the actual ambient (9.4) setting, suppose the moved remote vertex is an
initial-vertex neighbor distinct from the next vertex. The initial-core
conjugate closure of the conjugated actor lies in the intersection of the
initial and moved-remote cores. In particular, it lies in the literal
auxiliary subgroup used in the noncentral case of (9.4).

The module-centralizer theorem first places the conjugated actor in the
moved-remote core. The conjugator belongs to the next stabilizer, so the
conjugated actor also fixes the next vertex. At the initial vertex the
local quotient is SL₂(2) by (9.3): an element fixing two distinct neighbors
fixes the third, hence belongs to the initial core. Closing under the
initial core preserves this containment; the opening reduction of (9.4)
already supplies containment of the closure in the moved-remote core.

Source: Stellmacher (9.4), printed p.51/PDF p.41, the actor closure used to
place the selected factor in the auxiliary group, in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_actor_closure_le_core_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2)
    (actor : G)
    (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∈ Subgroup.centralizer (VAt ctx.Γ remote : Set G))
    (conjugator : G)
    (hconjugator : conjugator ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep,
      Subgroup.zpowers actor⁆)
    (hremote : ctx.Γ.act conjugator remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act conjugator remote ≠ ctx.criticalPath.firstStep) :
    conjugateClosure (Subgroup.zpowers (conjugator⁻¹ * actor * conjugator))
      (QAt ctx.Γ ctx.criticalPath.a) ≤
      QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ (ctx.Γ.act conjugator remote) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let moved := Γ.act conjugator remote
  let conjugated := conjugator⁻¹ * actor * conjugator
  have hadj : Γ.adjacent cp.a moved := (mem_neighborhood_iff_adjacent Γ).mp hremote
  have hreverse : cp.a ∈ Neighborhood Γ moved :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hadj)
  have hconjugated : conjugated ∈ QAt Γ moved :=
    nine_four_conjugated_actor_mem_remote_core ctx remote hdistance actor hactor
      conjugator hconjugator
  have hremoteSelf : QAt Γ moved ≤ GAt Γ moved := by
    change Γ.twoCoreAt moved ≤ Γ.vertexStabilizer moved
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hinitial : conjugated ∈ GAt Γ cp.a :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core moved cp.a
      hreverse default).2.2 hconjugated
  have hconjugatorNext := nine_four_conjugator_mem_stabilizer Γ cp.firstStep
    actor conjugator hactor.1 hconjugator
  have hnext : conjugated ∈ GAt Γ cp.firstStep :=
    (GAt Γ cp.firstStep).mul_mem
      ((GAt Γ cp.firstStep).mul_mem
        ((GAt Γ cp.firstStep).inv_mem hconjugatorNext) hactor.1) hconjugatorNext
  have hmodel := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).1
  have hinitialCore : conjugated ∈ QAt Γ cp.a :=
    cubic_mem_core_of_fix_two_neighbors Γ cp.a moved cp.firstStep
      (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.a hmodel)
      hadj cp.firstStep_adj hne ⟨conjugated, hinitial⟩
      ((Set.ext_iff.mp (Γ.stabilizer_def moved) conjugated).mp
        (hremoteSelf hconjugated))
      ((Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) conjugated).mp hnext)
  refine le_inf ?_ (nine_four_actor_closure_le_remote_core ctx remote hdistance actor
    hactor conjugator hconjugator cp.a hreverse)
  apply (Subgroup.closure_le _).mpr
  rintro point ⟨mover, element, rfl⟩
  have helement := (Subgroup.zpowers_le.mpr hinitialCore) element.property
  exact (QAt Γ cp.a).mul_mem
    ((QAt Γ cp.a).mul_mem mover.property helement)
    ((QAt Γ cp.a).inv_mem mover.property)

end Stellmacher.SectionNine
