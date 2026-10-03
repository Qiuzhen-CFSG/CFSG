module
public import Stellmacher.SectionNine.NineThreeGeometricExtraction
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.NeighborCenterNormalizer

/-!
# The extracted neighboring center escapes a supplied vertex core

Keep the exact geometric extraction data used in (9.3). If its prescribed
actor lies in the center at a supplied base vertex and that center
centralizes its core, the extracted neighboring center cannot lie in that
core. The original initial-vertex theorem remains a wrapper deriving
centralization from (7.3); the generic theorem also serves the second
extraction without choosing a differently normalized critical path.

If the extracted center lay in the base core, the prescribed center actor
would centralize it. The conjugated actor subgroup lies in the extracted
core and also centralizes its center. Generation therefore makes E
centralize that center, and edge generation makes the other stabilizer
normalize it. Adjacent stabilizers generate the whole graph group, so
this nontrivial two-subgroup would lie in the trivial global two-core.
The shared Section Seven neighbor-center normalizer theorem supplies this
last contradiction; its nontriviality comes from the edge Sylow omega-center.

All subgroups and the right-action vertex Γ.act x⁻¹ l are those of the
supplied geometric data. Source: Stellmacher (9.3), Journal of Algebra
190 (1997), p.49, after (i)–(v) and the repeated argument following (3),
`refs/files/stellmacher-n-group.pdf`.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- Geometric extraction escapes the core at any supplied base vertex whose
center contains the prescribed actor and centralizes that core. -/
public theorem nine_three_geometric_extracted_center_not_le_core
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B)
    (u0 d l : Γ.Vertex) (V E A0 : Subgroup G)
    (actor : G) (haV : actor ∈ V) (haZ : actor ∈ ZAt Γ u0)
    (hZu : ZAt Γ u0 ≤ Subgroup.centralizer (QAt Γ u0 : Set G))
    (data : NineThreeGeometricData Γ d l V E A0 actor) :
    ¬ ZAt Γ (Γ.act data.x⁻¹ l) ≤ QAt Γ u0 := by
  let m := Γ.act data.x⁻¹ l
  have hmrev : d ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hZm : ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) :=
    ((lemma_seven_three h Γ).center_core m d hmrev).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  intro hcontained
  have haC : actor ∈ Subgroup.centralizer (ZAt Γ m : Set G) :=
    (Subgroup.centralizer_le hcontained) (hZu haZ)
  have hVC : V.conjBy data.x ≤ Subgroup.centralizer (ZAt Γ m : Set G) :=
    data.conjugate_core_le.trans (Subgroup.le_centralizer_iff.mp hZm)
  have hEC : E ≤ Subgroup.centralizer (ZAt Γ m : Set G) := by
    rw [data.actor_generated actor haV data.actor_outside]
    exact sup_le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr haC)) hVC
  apply neighbor_center_not_normalized h Γ d m data.neighbor
  rw [← data.edge_generated]
  exact sup_le (hEC.trans (Subgroup.centralizer_le_normalizer _))
    (inf_le_right.trans (stabilizer_le_normalizer_z Γ m))

public theorem nine_three_extracted_center_not_le_initial_core
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (d l : ctx.Γ.Vertex) (V E A0 : Subgroup G)
    (actor : G) (haV : actor ∈ V) (haZ : actor ∈ ZAt ctx.Γ ctx.criticalPath.a)
    (data : NineThreeGeometricData ctx.Γ d l V E A0 actor) :
    ¬ ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ≤ QAt ctx.Γ ctx.criticalPath.a := by
  have hfirst : ctx.criticalPath.firstStep ∈ neighborhood ctx.Γ ctx.criticalPath.a :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  have hZa : ZAt ctx.Γ ctx.criticalPath.a ≤
      Subgroup.centralizer (QAt ctx.Γ ctx.criticalPath.a : Set G) :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core
      ctx.criticalPath.a ctx.criticalPath.firstStep hfirst).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  exact nine_three_geometric_extracted_center_not_le_core ctx.sectionSeven ctx.Γ
    ctx.criticalPath.a d l V E A0 actor haV haZ hZa data
end Stellmacher.SectionNine
