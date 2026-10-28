module
public import Stellmacher.SectionNine.NineFourFactorAuxiliaryImage
public import Stellmacher.SectionOne.OneSevenFactorAction
public import Stellmacher.SectionThree.ConjugateClosureResidual

/-!
# Conjugate generation of the literal auxiliary residual image

In the normalized (9.4) setup, use the exact local quotient map and the
canonical Section One factor supplied by the transvection packet. The
image of the literal residual O²(F) is the conjugate closure of that factor's
derived subgroup under the image of the initial/remote core intersection.
The statement retains both the ambient subgroup and its restricted quotient
map, so the subsequent auxiliary-module argument can use this equality
directly with the original conjugation action.

The auxiliary-image theorem writes F's image as the join of the selected
derived subgroup and the core-intersection image. The former lies in the
global three-core by the canonical factor theorem; the latter is a two-group.
The odd-core conjugate-closure residual theorem therefore computes O² of
that image. Residual functoriality, first through the subgroup inclusion
and then through the quotient map, identifies it with the image of O²(F).

Source: Stellmacher (9.4)(1), printed p.51/PDF p.41, the conjugate-generation
formula immediately after the choice of the first factor, in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_factor_residual_image
    {H G K W : Type u} [Group H] [Finite H] [Group G] [Finite G]
    [Group K] [Finite K] [Group W] [Finite W] [MulDistribMulAction K W]
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
    (hne : ctx.Γ.act conjugator remote ≠ ctx.criticalPath.firstStep)
    (hgenerate : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ ctx.criticalPath.a) ⊔
      Subgroup.zpowers actor = GAt ctx.Γ ctx.criticalPath.firstStep)
    (f : GAt ctx.Γ ctx.criticalPath.firstStep →* K) (hsurj : Function.Surjective f)
    (hkernel : f.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hinvolution : _root_.IsInvolution (f ⟨actor, hactor.1⟩))
    (hfactor : SectionOne.IsOneSevenFactor (V := W)
      (⁅SectionOne.oddCore K, Subgroup.zpowers (f ⟨actor, hactor.1⟩)⁆ ⊔
        Subgroup.zpowers (f ⟨actor, hactor.1⟩))) :
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let R0 := QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ (ctx.Γ.act conjugator remote)
    let F := R0 ⊔ Subgroup.zpowers actor
    let t := f ⟨actor,hactor.1⟩
    let D := ⁅SectionOne.oddCore K, Subgroup.zpowers t⁆ ⊔ Subgroup.zpowers t
    ((twoResidualIn F).subgroupOf P).map f =
      conjugateClosure ((commutator D).map D.subtype) ((R0.subgroupOf P).map f) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  let R0 := Qa ⊓ QAt Γ (Γ.act conjugator remote)
  let F := R0 ⊔ Subgroup.zpowers actor
  let D := ⁅SectionOne.oddCore K, Subgroup.zpowers (f ⟨actor,hactor.1⟩)⁆ ⊔
    Subgroup.zpowers (f ⟨actor,hactor.1⟩)
  have hpacket := nine_four_factor_le_auxiliary_image ctx hb remote hdistance actor hactor
    conjugator hconjugator hremote hne hgenerate f hsurj hkernel hinvolution hfactor.1
  have hQaP : Qa ≤ P :=
    ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans cp.S_le_edge_stabilizers).trans
      inf_le_right
  have hFP : F ≤ P := sup_le (inf_le_left.trans hQaP) (Subgroup.zpowers_le.mpr hactor.1)
  have hsub : (twoResidualIn F).subgroupOf P = twoResidualAmbient (F.subgroupOf P) := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((twoResidualIn_le F).trans hFP)]
    exact (map_twoResidualAmbient_of_subgroup_image (F.subgroupOf P) P.subtype F
      (Subgroup.map_subgroupOf_eq_of_le hFP)).symm
  have hresImage : ((twoResidualIn F).subgroupOf P).map f =
      twoResidualAmbient ((F.subgroupOf P).map f) := by
    rw [hsub]
    exact map_twoResidualAmbient_of_subgroup_image _ _ _ rfl
  have hRtwo : IsPGroup 2 ((R0.subgroupOf P).map f) := by
    have hQaTwo : IsPGroup 2 Qa := by
      change IsPGroup 2 (q Γ cp.a)
      rw [q,Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := GAt Γ cp.a)).map (GAt Γ cp.a).subtype
    exact ((hQaTwo.to_le (show R0 ≤ Qa from inf_le_left)).comap_subtype).map f
  change ((twoResidualIn F).subgroupOf P).map f = _
  rw [hresImage,hpacket.2]
  exact SectionThree.twoResidualAmbient_sup_eq_conjugateClosure
    ((commutator D).map D.subtype) ((R0.subgroupOf P).map f) Nat.prime_three
    (by decide) (SectionOne.oneSevenFactor_derived_le_threeCore D hfactor) hRtwo

end Stellmacher.SectionNine
