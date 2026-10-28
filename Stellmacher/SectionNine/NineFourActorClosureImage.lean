module
public import Stellmacher.SectionNine.NineFourActorClosureAction
public import Stellmacher.SectionOne.OneSevenGlobalProduct

/-!
# The actor closure inside the global canonical factor product

For the actual normalized (9.4) actor and conjugator, use the supplied local
quotient homomorphism and its Section One canonical factor. The literal
actor-closure image Tbar lies in the global one-seven product. The initial
core image normalizes Tbar, and Tbar normalizes the selected factor. This
retains the exact action and quotient map needed for source (5).

The global factor product is normal and contains the actor image. Its
normal preimage in the local stabilizer therefore contains the conjugated
actor and every initial-core conjugate, hence T. The proved normalization
of T by the initial core descends under the homomorphism. Finally every
canonical factor is normal in the global internal product, so membership
of Tbar in that product gives normalization of the selected factor.
No additional kernel or surjectivity assumption is needed for these
particular image containments.

Source: Stellmacher (9.4)(1) and the noncentral auxiliary case, printed
p.51/PDF p.41 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_actor_closure_image
    {G K W : Type u} [Group G] [Finite G] [Group K] [Finite K]
    [Group W] [Finite W] [IsElementaryAbelian 2 W] [MulDistribMulAction K W]
    {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (remote : ctx.Γ.Vertex) (actor : G)
    (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∈ Subgroup.centralizer (VAt ctx.Γ remote : Set G))
    (conjugator : G)
    (hconjugator : conjugator ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep,
      Subgroup.zpowers actor⁆)
    (hremote : ctx.Γ.act conjugator remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (f : GAt ctx.Γ ctx.criticalPath.firstStep →* K)
    (hyp : SectionOne.Hypotheses K W)
    (hfactor : SectionOne.IsOneSevenFactor (V := W)
      (⁅SectionOne.oddCore K, Subgroup.zpowers (f ⟨actor,hactor.1⟩)⁆ ⊔
        Subgroup.zpowers (f ⟨actor,hactor.1⟩))) :
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let Qa := QAt ctx.Γ ctx.criticalPath.a
    let T0 := conjugateClosure (Subgroup.zpowers (conjugator⁻¹*actor*conjugator)) Qa
    let Tbar := (T0.subgroupOf P).map f
    let D := ⁅SectionOne.oddCore K, Subgroup.zpowers (f ⟨actor,hactor.1⟩)⁆ ⊔
      Subgroup.zpowers (f ⟨actor,hactor.1⟩)
    Tbar ≤ SectionOne.oneSevenGenerated (G := K) (V := W) ∧
      (Qa.subgroupOf P).map f ≤ Subgroup.normalizer (Tbar : Set K) ∧
      Tbar ≤ Subgroup.normalizer (D : Set K) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  let u := conjugator⁻¹*actor*conjugator
  let T0 := conjugateClosure (Subgroup.zpowers u) Qa
  let D := ⁅SectionOne.oddCore K, Subgroup.zpowers (f ⟨actor,hactor.1⟩)⁆ ⊔
    Subgroup.zpowers (f ⟨actor,hactor.1⟩)
  let E := SectionOne.oneSevenGenerated (G := K) (V := W)
  have hglobal := SectionOne.oneSeven_global_product hyp (default : Sylow 2 K)
  let _ : E.Normal := hglobal.1
  let N := E.comap f
  let M := N.map P.subtype
  have hMP : M ≤ P := Subgroup.map_subtype_le _
  have hMnormal : (M.subgroupOf P).Normal := by
    change ((N.map P.subtype).subgroupOf P).Normal
    rw [subgroupOf_map_subtype_eq]
    exact inferInstance
  have hPM : P ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMP).mp hMnormal
  have hQaP : Qa ≤ P :=
    ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans cp.S_le_edge_stabilizers).trans
      inf_le_right
  have hxP := nine_four_conjugator_mem_stabilizer Γ cp.firstStep actor conjugator
    hactor.1 hconjugator
  have hDE : D ≤ E := le_sSup hfactor
  have htM : actor ∈ M := by
    refine ⟨⟨actor,hactor.1⟩,?_,rfl⟩
    change f ⟨actor,hactor.1⟩ ∈ E
    exact hDE (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have huM : u ∈ M := by
    have hh := (Subgroup.mem_normalizer_iff.mp (hPM (P.inv_mem hxP)) actor).mp htM
    simpa only [u,inv_inv] using hh
  have hTM : T0 ≤ M := by
    apply (Subgroup.closure_le _).mpr
    rintro point ⟨mover,element,rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hPM (hQaP mover.property)) element).mp
      ((Subgroup.zpowers_le.mpr huM) element.property)
  have hTP : T0 ≤ P := hTM.trans hMP
  have hTimage : (T0.subgroupOf P).map f ≤ E := by
    apply Subgroup.map_le_iff_le_comap.mpr
    have hh := Subgroup.subgroupOf_mono P hTM
    rwa [show M = N.map P.subtype from rfl,subgroupOf_map_subtype_eq] at hh
  have hQaT : Qa ≤ Subgroup.normalizer (T0 : Set G) :=
    (nine_four_actor_closure_action ctx remote actor hactor.2 conjugator hremote).2
  have hQaTnative : Qa.subgroupOf P ≤ Subgroup.normalizer (T0.subgroupOf P) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTP]
    exact Subgroup.subgroupOf_mono P hQaT
  have hQabarT : (Qa.subgroupOf P).map f ≤ Subgroup.normalizer ((T0.subgroupOf P).map f) :=
    (Subgroup.map_mono hQaTnative).trans (Subgroup.le_normalizer_map f)
  have hDn : (D.subgroupOf E).Normal :=
    hglobal.2.1.2.1 D ((SectionOne.mem_oneSevenFactors_iff D).mpr hfactor)
  exact ⟨hTimage,hQabarT,hTimage.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hDE).mp hDn)⟩

end Stellmacher.SectionNine
