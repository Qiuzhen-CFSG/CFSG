module
public import Stellmacher.SectionNine.NineThreeSecondSmallFixedSubgroup
public import Stellmacher.SectionNine.NineThreeSecondCenterInputs
public import Stellmacher.SectionNine.NineThreeGeometricCenterIntersections

/-!
# Center intersections for the second extraction in (9.3)

Assume the initial center has order greater than four and retain both actual
geometric extractions. Intersecting the second new center with the first
extracted core equals its intersection with the second path center. This
intersection has index at most two inside the first-extracted stabilizer
intersection, and the second new center escapes that stabilizer.

The second small fixed subgroup supplies W. Reverse-path critical minimality,
endpoint alignment and local transitivity give the geometric containment and
cardinality inputs. Apply the common center-intersection argument, which
uses the exact arbitrary-edge (9.2). Thus the 'same argument' in the source
has all of its orbit, module, core and order hypotheses supplied explicitly.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), p.49, immediately
after (3), `refs/files/stellmacher-n-group.pdf`. These are the inputs for
replacing the initial vertex by the second extracted neighbor.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_second_center_relations
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first) :
    let m := ctx.Γ.act first.extraction.x⁻¹ first.l
    let n := ctx.Γ.act second.extraction.x⁻¹ second.l
    ZAt ctx.Γ n ⊓ QAt ctx.Γ m = ZAt ctx.Γ n ⊓ ZAt ctx.Γ second.l ∧
      Nat.card (ZAt ctx.Γ n ⊓ GAt ctx.Γ m : Subgroup G) ≤
        2 * Nat.card (ZAt ctx.Γ n ⊓ QAt ctx.Γ m : Subgroup G) ∧
      ¬ ZAt ctx.Γ n ≤ GAt ctx.Γ m := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  obtain ⟨hmorbit,hd,hl,hZlQ,hcard,hZmC⟩ := nine_three_second_center_inputs ctx hb first second
  have hVQ : VAt Γ cp.a' ≤ QAt Γ second.l := by
    obtain ⟨hsecond,hsecondEq⟩ := second.second
    rw [hsecondEq]
    exact (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.1
  have hZmV : ZAt Γ m ≤ VAt Γ cp.a' := by
    change z Γ m ≤ v Γ cp.a'
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨m,first.extraction.neighbor,rfl⟩
  have hlargeL : 4 < Nat.card (ZAt Γ second.l) := by rw [hcard]; exact hlarge
  obtain ⟨W,hWn,hWm,hWl,hbound,hEC,hescape⟩ :=
    nine_three_second_small_fixed_subgroup ctx hb first second
  exact nine_three_geometric_center_intersections ctx m cp.firstStep second.l hd hl
    (VAt Γ cp.a') second.E second.A0 hVQ second.actor (hZmV second.actor_first_center)
    second.actor_first_center hZmC hZlQ hlargeL second.extraction W hWn hWm hWl hbound

end Stellmacher.SectionNine
