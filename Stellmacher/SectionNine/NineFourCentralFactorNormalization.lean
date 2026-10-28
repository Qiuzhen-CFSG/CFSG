module
public import Stellmacher.SectionNine.NineFourNormalizedEnlarged
public import Stellmacher.SectionNine.NineFourFactorAuxiliaryImage
public import Stellmacher.SectionNine.NineFourAuxiliaryCore
public import Stellmacher.SectionOne.OneSevenFactorSL2ImageNormalizer
public import Stellmacher.SectionOne.SL2DerivedSupplementFullImage
public import Theory.GroupAction.QuotientConjugationImageDescent

/-!
# Selected-factor normalization from the central core quotient action

Take the exact normalized counterexample data from (9.4) and its supplied
faithful next-module quotient map and canonical factor D. Suppose the
literal auxiliary group F has its conjugation action on the abelian core
quotient Q_next/Qstar, with action image SL₂(2). Then the image of
Q_a intersect Q_remote normalizes D. The theorem retains the supplied
core-quotient normality witness, action, and representative formula.

Inner conjugation by Q_next is trivial on the abelian core quotient.
Consequently the F-action descends through the actual next-core quotient
map to Fbar, with the same action image. The proved auxiliary image
identity is Fbar=D' joined with Rbar, where Rbar is a two-group. The
derived-supplement image theorem makes D map onto the full SL₂(2) action
image. Distinct canonical factors commute, so two distinct Fbar-conjugate
factors could not both have that full nonabelian image. Thus Fbar, and
hence Rbar, normalizes D.

This gives the exact input of `nine_four_actor_cover_of_factor_normalization`
in the central branch of Stellmacher (9.4), printed pp.51–52 / PDF
pp.41–42 of `refs/files/stellmacher-n-group.pdf`. The quotient action and
its SL₂(2) identification are separate actual-input producers; no factor
normalization or kernel identification is assumed here.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_central_factor_normalization
    {H G K V : Type u} [Group H] [Finite H] [Group G] [Finite G]
    [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (data : NineFourCounterexample ctx)
    (hremote : ctx.Γ.act data.conjugator data.remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act data.conjugator data.remote ≠ ctx.criticalPath.firstStep)
    (f : GAt ctx.Γ ctx.criticalPath.firstStep →* K) (hsurj : Function.Surjective f)
    (hkernel : f.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hinvolution : _root_.IsInvolution (f ⟨data.actor,data.actor_mem⟩))
    (hyp : SectionOne.Hypotheses K V)
    (hfactor : SectionOne.IsOneSevenFactor (V:=V)
      (⁅SectionOne.oddCore K,Subgroup.zpowers (f ⟨data.actor,data.actor_mem⟩)⁆ ⊔
        Subgroup.zpowers (f ⟨data.actor,data.actor_mem⟩))) :
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let U := QAt ctx.Γ ctx.criticalPath.firstStep
    let N := QAt ctx.Γ ctx.criticalPath.a ⊓ U
    let R := QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote)
    let F := R ⊔ Subgroup.zpowers data.actor
    let C := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
    ∀ hN : (C.subgroupOf U).Normal,
      let _ := hN
      ∀ (_habelian : IsMulCommutative (U ⧸ C.subgroupOf U))
        (action : F →* MulAut (U ⧸ C.subgroupOf U)),
        (∀ mover : F, ∀ point : U,
          ∃ hconj : (mover : G)*(point : G)*(mover : G)⁻¹ ∈ U,
            action mover (QuotientGroup.mk' (C.subgroupOf U) point) =
              QuotientGroup.mk' (C.subgroupOf U)
                ⟨(mover : G)*(point : G)*(mover : G)⁻¹,hconj⟩) →
        IsSL2Two action.range →
        (R.subgroupOf P).map f ≤ Subgroup.normalizer
          (⁅SectionOne.oddCore K,Subgroup.zpowers (f ⟨data.actor,data.actor_mem⟩)⁆ ⊔
            Subgroup.zpowers (f ⟨data.actor,data.actor_mem⟩) : Subgroup K) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let U := QAt Γ cp.firstStep
  let N := QAt Γ cp.a ⊓ U
  let d := Γ.act data.conjugator data.remote
  let R := QAt Γ cp.a ⊓ QAt Γ d
  let F := R ⊔ Subgroup.zpowers data.actor
  let C := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
  let D := ⁅SectionOne.oddCore K,Subgroup.zpowers (f ⟨data.actor,data.actor_mem⟩)⁆ ⊔
    Subgroup.zpowers (f ⟨data.actor,data.actor_mem⟩)
  let Fbar := (F.subgroupOf P).map f
  let Rbar := (R.subgroupOf P).map f
  dsimp only
  intro hN
  let _ := hN
  intro habelian action hact himage
  have hFP : F ≤ P := (nine_four_auxiliary_core_geometry ctx hb d data.actor data.actor_mem).1
  have hFU : F ≤ Subgroup.normalizer U := hFP.trans (stabilizer_le_normalizer_q Γ cp.firstStep)
  have hker : f.ker = U.subgroupOf P := by
    rw [hkernel]
    change pCore 2 P = (Γ.twoCoreAt cp.firstStep).subgroupOf P
    rw [Γ.twoCoreAt_def]
    exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm
  have hact' : ∀ mover : F, ∀ point : U,
      action mover (QuotientGroup.mk' (C.subgroupOf U) point) =
        QuotientGroup.mk' (C.subgroupOf U)
          ⟨(mover : G)*(point : G)*(mover : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hFU mover.property) point).mp point.property⟩ := by
    intro mover point
    obtain ⟨hconj,heq⟩ := hact mover point
    exact heq
  obtain ⟨descended,hdescSurj,_hcompat⟩ :=
    Subgroup.quotient_conjugation_image_descent P F U C hFP hFU f hker hN
      habelian action hact'
  have hgen := data.generates cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    ((mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote)))
  have hfactorImage := nine_four_factor_le_auxiliary_image ctx hb data.remote data.distance
    data.actor ⟨data.actor_mem,data.actor_centralizes⟩ data.conjugator data.conjugator_mem
    hremote hne hgen f hsurj hkernel hinvolution hfactor.1
  have hRF : Rbar ≤ Fbar := Subgroup.map_mono (Subgroup.subgroupOf_mono P le_sup_left)
  have hQaTwo : IsPGroup 2 (QAt Γ cp.a) := by
    change IsPGroup 2 (Γ.twoCoreAt cp.a)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := GAt Γ cp.a)).map _
  have hRtwo : IsPGroup 2 Rbar := ((hQaTwo.to_le (show R ≤ QAt Γ cp.a from inf_le_left)).comap_subtype).map f
  have hfull := SectionOne.sl2_factor_image_eq_top_of_derived_supplement D Fbar Rbar hfactorImage.1 hRF hfactor.1 hRtwo
    hfactorImage.2 descended hdescSurj himage
  exact hRF.trans (SectionOne.oneSevenFactor_normalized_of_full_sl2_image hyp D Fbar
    hfactor descended himage hfull)

end Stellmacher.SectionNine
