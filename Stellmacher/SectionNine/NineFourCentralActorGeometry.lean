module
public import Stellmacher.SectionNine.NineNextTransvectionActor

/-!
# The actor square and core-intersection nonnormality in central (9.4)

For the actual next-stabilizer actor satisfying the displacement-cardinality
condition of (9.4), its square lies in the next core. If adjoining it to
the edge stabilizer generates the next stabilizer, the actor cannot
normalize the initial/next core intersection. These assertions use only
the original actor data; no auxiliary quotient or factor conclusion is
assumed.

The literal transvection action has involutive actor image and exactly
the next two-core as its kernel, which proves the square containment.
Both endpoint stabilizers normalize their own cores, so the edge
normalizes the core intersection. If the actor did too, the generating
hypothesis would make the intersection normal in the next stabilizer,
contrary to (7.6)(a).

This supplies the actor geometry for the four-element conjugate-core
quotient in the all-central case of Stellmacher (9.4), printed pp.51–52 /
PDF pp.41–42 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_central_actor_geometry
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hgenerate : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ ctx.criticalPath.a) ⊔
      Subgroup.zpowers actor = GAt ctx.Γ ctx.criticalPath.firstStep)
    (hdisplacement : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep)
      (ZAt ctx.Γ ctx.criticalPath.firstStep) 2) :
    actor ^ 2 ∈ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ Subgroup.normalizer
        (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let N := QAt Γ cp.a ⊓ QAt Γ cp.firstStep
  obtain ⟨hN,hW,action,_hact,hkernel,hinv,_horder,_hrank⟩ :=
    nine_next_transvection_actor ctx hb cp.firstStep ⟨1,Γ.act_one _⟩
      ⟨actor,hactor⟩ hdisplacement
  let _ := hN
  let _ := hW
  have hsquare : (⟨actor,hactor⟩ : P)^2 ∈ pCore 2 P := by
    rw [← hkernel,MonoidHom.mem_ker,map_pow]
    exact hinv.2
  have hsquareAmbient : actor^2 ∈ QAt Γ cp.firstStep := by
    change actor^2 ∈ Γ.twoCoreAt cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact Subgroup.mem_map.mpr ⟨(⟨actor,hactor⟩ : P)^2,hsquare,rfl⟩
  refine ⟨hsquareAmbient,?_⟩
  intro hnormal
  have hEdge : GAt Γ cp.firstStep ⊓ GAt Γ cp.a ≤ Subgroup.normalizer N :=
    (le_inf (inf_le_right.trans (stabilizer_le_normalizer_q Γ cp.a))
      (inf_le_left.trans (stabilizer_le_normalizer_q Γ cp.firstStep))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hPN : P ≤ Subgroup.normalizer N := by
    exact hgenerate.symm.le.trans (sup_le hEdge (Subgroup.zpowers_le.mpr hnormal))
  have hNP : N ≤ P := by
    apply inf_le_right.trans
    change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  exact (lemma_seven_six ctx.sectionSeven Γ cp).core_intersection_not_normal
    ⟨hNP,(Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN⟩

end Stellmacher.SectionNine
