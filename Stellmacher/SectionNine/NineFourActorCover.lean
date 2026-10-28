module
public import Stellmacher.SectionNine.NineFourCoreImageSylow
public import Stellmacher.SectionNine.NineFourActorClosureImage
public import Stellmacher.SectionNine.NineFourConjugatedActorImage
public import Stellmacher.SectionNine.NineFourActorClosure
public import Stellmacher.SectionOne.OneSevenSylowFactorClosure

/-!
# The actor closure covers the auxiliary core intersection

For the normalized (9.4) setup and the supplied faithful local quotient,
suppose the image of the initial/remote core intersection normalizes the
selected canonical factor. Then that literal core intersection lies in
the actor closure times the next core. The factor-normalization premise
is produced by the noncentral support equality and separately in the
all-central argument.

The initial-core image is an actual Sylow subgroup and normalizes the
core-intersection image. The conjugated actor is an involution of the
selected factor lying in that intersection. The canonical Sylow-factor
closure theorem puts the whole image in its Sylow conjugate closure.
The actual actor-closure image is Sylow-invariant and contains that
involution, so it contains this closure. Pullback through the exact
supplied kernel gives the asserted ambient containment.

Source: Stellmacher (9.4), printed p.51/PDF p.41, the assertion
T≤Q_a intersect Q_remote≤T Q_next following relation (5), reused in the
all-central case on printed p.52.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_actor_cover_of_factor_normalization
    {H G K V : Type u} [Group H] [Finite H] [Group G] [Finite G]
    [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
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
    (hconjugator : conjugator ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep,Subgroup.zpowers actor⁆)
    (hremote : ctx.Γ.act conjugator remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act conjugator remote ≠ ctx.criticalPath.firstStep)
    (hgenerate : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ ctx.criticalPath.a) ⊔
      Subgroup.zpowers actor = GAt ctx.Γ ctx.criticalPath.firstStep)
    (f : GAt ctx.Γ ctx.criticalPath.firstStep →* K) (hsurj : Function.Surjective f)
    (hkernel : f.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hinvolution : _root_.IsInvolution (f ⟨actor,hactor.1⟩))
    (hyp : SectionOne.Hypotheses K V)
    (hfactor : SectionOne.IsOneSevenFactor (V:=V)
      (⁅SectionOne.oddCore K,Subgroup.zpowers (f ⟨actor,hactor.1⟩)⁆ ⊔
        Subgroup.zpowers (f ⟨actor,hactor.1⟩)))
    (hnormal : ((QAt ctx.Γ ctx.criticalPath.a ⊓
        QAt ctx.Γ (ctx.Γ.act conjugator remote)).subgroupOf
          (GAt ctx.Γ ctx.criticalPath.firstStep)).map f ≤ Subgroup.normalizer
        (⁅SectionOne.oddCore K,Subgroup.zpowers (f ⟨actor,hactor.1⟩)⁆ ⊔
          Subgroup.zpowers (f ⟨actor,hactor.1⟩) : Subgroup K)) :
    QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ (ctx.Γ.act conjugator remote) ≤
      conjugateClosure (Subgroup.zpowers (conjugator⁻¹*actor*conjugator))
        (QAt ctx.Γ ctx.criticalPath.a) ⊔ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  let Qn := QAt Γ cp.firstStep
  let d := Γ.act conjugator remote
  let R := Qa ⊓ QAt Γ d
  let C := conjugateClosure (Subgroup.zpowers (conjugator⁻¹*actor*conjugator)) Qa
  let Sbar := (Qa.subgroupOf P).map f
  let Rbar := (R.subgroupOf P).map f
  let Cbar := (C.subgroupOf P).map f
  let t : P := ⟨actor,hactor.1⟩
  let x : P := ⟨conjugator,nine_four_conjugator_mem_stabilizer Γ cp.firstStep actor
    conjugator hactor.1 hconjugator⟩
  let u : P := x⁻¹*t*x
  let D := ⁅SectionOne.oddCore K,Subgroup.zpowers (f t)⁆ ⊔ Subgroup.zpowers (f t)
  obtain ⟨sylow,hS,hRle,hRnormal,hgen⟩ := nine_four_core_image_sylow ctx hb d hremote
    actor hactor.1 hgenerate f hsurj hkernel
  change (sylow : Subgroup K) = Sbar at hS
  change Rbar ≤ Sbar at hRle
  change (Rbar.subgroupOf Sbar).Normal at hRnormal
  change Sbar ⊔ Subgroup.zpowers (f t) = ⊤ at hgen
  rw [← hS] at hRle hRnormal hgen
  have hDgen : D ⊔ (sylow : Subgroup K) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
  have hconjugated := nine_four_conjugated_actor_image ctx.toLocalContext actor hactor.1
    conjugator hconjugator f hsurj hkernel hinvolution
  have hCR : C ≤ R := nine_four_actor_closure_le_core_intersection ctx hb remote hdistance
    actor hactor conjugator hconjugator hremote hne
  have huC : (u:G) ∈ C := by
    apply Subgroup.subset_closure
    refine ⟨1,⟨conjugator⁻¹*actor*conjugator,Subgroup.mem_zpowers _⟩,?_⟩
    simp [u,x,t]
  have huR : f u ∈ Rbar := Subgroup.mem_map_of_mem f (hCR huC)
  have hRclosure : Rbar ≤ Stellmacher.conjugateClosure (Subgroup.zpowers (f u))
      (sylow : Subgroup K) :=
    SectionOne.oneSevenFactor_sylow_normal_subgroup_le_conjugateClosure hyp D hfactor
      sylow Rbar hRle hRnormal hnormal hDgen (f u) hconjugated.1 huR hconjugated.2.1
  have himage := nine_four_actor_closure_image ctx.toLocalContext remote actor hactor
    conjugator hconjugator hremote f hyp hfactor
  have hSnorm : (sylow : Subgroup K) ≤ Subgroup.normalizer Cbar := hS ▸ himage.2.1
  have hclosureC : Stellmacher.conjugateClosure (Subgroup.zpowers (f u))
      (sylow : Subgroup K) ≤ Cbar := by
    apply (Subgroup.closure_le _).mpr
    rintro element ⟨s,c,rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hSnorm s.property) c).mp
      ((Subgroup.zpowers_le.mpr hconjugated.2.2) c.property)
  have hRCbar : Rbar ≤ Cbar := hRclosure.trans hclosureC
  have hQaP : Qa ≤ P := ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans
    cp.S_le_edge_stabilizers).trans inf_le_right
  have hRP : R ≤ P := inf_le_left.trans hQaP
  have hCP : C ≤ P := hCR.trans hRP
  have hpreimage : R.subgroupOf P ≤ C.subgroupOf P ⊔ f.ker := by
    have hh := Subgroup.map_le_iff_le_comap.mp hRCbar
    rwa [Subgroup.comap_map_eq] at hh
  have hkernelMap : f.ker.map P.subtype = Qn := by
    rw [hkernel]
    change (pCore 2 P).map P.subtype = Γ.twoCoreAt cp.firstStep
    rw [Γ.twoCoreAt_def]
    rfl
  have hh := Subgroup.map_mono (f:=P.subtype) hpreimage
  rwa [Subgroup.map_subgroupOf_eq_of_le hRP,Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hCP,hkernelMap] at hh

end Stellmacher.SectionNine
