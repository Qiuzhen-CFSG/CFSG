module
public import Stellmacher.SectionNine.NineInitialEdgeCoreProduct

/-!
# The initial core image is the next local Sylow subgroup

For any supplied surjective next-stabilizer quotient map with kernel the
next two-core, the initial-core image is a Sylow two-subgroup. The image
of its intersection with a neighboring core is normal in that Sylow. If
the actor and initial edge generate the next stabilizer, their images
retain the same generation equality.

The initial and next cores generate the initial edge, and both lie in the
distinguished edge Sylow. Hence that edge is the distinguished Sylow.
After killing the next core, its image equals the initial-core image.
The initial core normalizes the neighboring core because it fixes each
neighbor. This normality descends under the supplied homomorphism.

Source: the remark after (9.3) and the sentence following (9.4)(5), printed
pp.50–51/PDF pp.40–41 of Stellmacher's `2-local structure of N-groups`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_core_image_sylow
    {H G K : Type u} [Group H] [Finite H] [Group G] [Finite G] [Group K] [Finite K]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex) (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hgenerate : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ ctx.criticalPath.a) ⊔
      Subgroup.zpowers actor = GAt ctx.Γ ctx.criticalPath.firstStep)
    (f : GAt ctx.Γ ctx.criticalPath.firstStep →* K) (hsurj : Function.Surjective f)
    (hkernel : f.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let Sbar := ((QAt ctx.Γ ctx.criticalPath.a).subgroupOf P).map f
    let Rbar := ((QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote).subgroupOf P).map f
    ∃ sylow : Sylow 2 K, (sylow : Subgroup K) = Sbar ∧
      Rbar ≤ Sbar ∧ (Rbar.subgroupOf Sbar).Normal ∧
      Sbar ⊔ Subgroup.zpowers (f ⟨actor,hactor⟩) = ⊤ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  let Qn := QAt Γ cp.firstStep
  let R := Qa ⊓ QAt Γ remote
  let t : P := ⟨actor,hactor⟩
  have hedge : Qa ⊔ Qn = GAt Γ cp.a ⊓ P := (nine_initial_edge_core_product ctx hb).1
  have hQaT : Qa ≤ T := (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hQnT : Qn ≤ T := (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2
  have hTedge : T = GAt Γ cp.a ⊓ P :=
    le_antisymm cp.S_le_edge_stabilizers (hedge ▸ sup_le hQaT hQnT)
  have hTP : T ≤ P := (edge_sylow_data ctx.sectionSeven Γ cp).2.1
  have hQaP : Qa ≤ P := hQaT.trans hTP
  have hQnP : Qn ≤ P := hQnT.trans hTP
  obtain ⟨_, original, horiginal⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).2
  have hTnative : T.subgroupOf P = (original : Subgroup P) := by
    calc
      T.subgroupOf P = ((original : Subgroup P).map P.subtype).subgroupOf P :=
        congrArg (fun J : Subgroup G => J.subgroupOf P) horiginal.symm
      _ = (original : Subgroup P) :=
        Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hTjoin : T.subgroupOf P = Qa.subgroupOf P ⊔ Qn.subgroupOf P := by
    rw [hTedge,← hedge,Subgroup.subgroupOf_sup hQaP hQnP]
  have hQnker : Qn.subgroupOf P = f.ker := by
    rw [hkernel]
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  let Sbar := (Qa.subgroupOf P).map f
  let Rbar := (R.subgroupOf P).map f
  have hSylowImage : ((original : Subgroup P).map f) = Sbar := by
    have hzero : f.ker.map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
    rw [← hTnative,hTjoin,Subgroup.map_sup,hQnker,hzero,sup_bot_eq]
  let sylow := original.mapSurjective hsurj
  have hRle : Rbar ≤ Sbar := Subgroup.map_mono (Subgroup.subgroupOf_mono P inf_le_left)
  have hQaR : Qa ≤ Subgroup.normalizer R :=
    (le_inf Qa.le_normalizer
      (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a remote
        hremote default).2.2.trans (stabilizer_le_normalizer_q Γ remote))).trans
          Subgroup.inf_normalizer_le_normalizer_inf
  have hQaNative : Qa.subgroupOf P ≤ Subgroup.normalizer (R.subgroupOf P) := by
    rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_left.trans hQaP)]
    exact Subgroup.subgroupOf_mono P hQaR
  have hSnorm : Sbar ≤ Subgroup.normalizer Rbar :=
    (Subgroup.map_mono hQaNative).trans (Subgroup.le_normalizer_map f)
  have hgenNative : T.subgroupOf P ⊔ Subgroup.zpowers t = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hTP,MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map,Subgroup.range_subtype,hTedge]
    change (GAt Γ cp.a ⊓ P) ⊔ Subgroup.zpowers actor = P
    simpa only [inf_comm] using hgenerate
  have hgen : Sbar ⊔ Subgroup.zpowers (f t) = ⊤ := by
    have hh := congrArg (fun J : Subgroup P => J.map f) hgenNative
    rw [Subgroup.map_sup,hTnative,hSylowImage,MonoidHom.map_zpowers,
      Subgroup.map_top_of_surjective f hsurj] at hh
    exact hh
  exact ⟨sylow,(Sylow.coe_mapSurjective hsurj original).trans hSylowImage,hRle,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRle).mpr hSnorm,hgen⟩

end Stellmacher.SectionNine
