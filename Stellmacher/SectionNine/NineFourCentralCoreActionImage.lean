module
public import Stellmacher.SectionNine.NineFourCentralActionRecognition
public import Stellmacher.SectionNine.NineFourCentralActorGeometry
public import Stellmacher.SectionNine.NineFourNormalizedEnlarged
public import Stellmacher.SectionNine.NineFourFactorAuxiliaryImage
public import Stellmacher.SectionNine.NineFourAuxiliaryCore
public import Theory.GroupAction.QuotientConjugationImageDescent

/-!
# The central core quotient action has image SL₂(2)

For the original normalized counterexample data in (9.4), retain the
actual next-core quotient map, its canonical SL₂(2) factor, and the
literal action of F on the elementary four-element quotient Q_next/Qstar.
This action has image SL₂(2). The supplied quotient normality witness
and representative formula are preserved throughout.

The abelian core quotient makes the action descend through the next-core
quotient map. The residual commutator conjugator lies in the canonical
factor, which lies in the image of F, so the actor and conjugated actor
have conjugate descended images. The original actor fails to normalize
Q_a intersect Q_next, while its conjugate lies in Q_a intersect Q_remote
and normalizes that intersection. Lifting the corresponding quotient
support therefore shows their action images are distinct and the first
is nontrivial. Its square is trivial by the original quotient involution
condition; conjugacy gives the same for the second. The faithful
action-image recognition theorem on a four-group finishes the proof.

This supplies the actual action-image input of central factor
normalization in Stellmacher (9.4), printed pp.51–52 / PDF pp.41–42 of
`refs/files/stellmacher-n-group.pdf`. The four-element cardinality is
proved separately by the conjugate-core index theorem.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_central_core_action_image
    {H G K : Type u} [Group H] [Finite H] [Group G] [Finite G]
    [Group K] [Finite K]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (data : NineFourCounterexample ctx)
    (hremote : ctx.Γ.act data.conjugator data.remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act data.conjugator data.remote ≠ ctx.criticalPath.firstStep)
    (f : GAt ctx.Γ ctx.criticalPath.firstStep →* K) (hsurj : Function.Surjective f)
    (hkernel : f.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hinvolution : _root_.IsInvolution (f ⟨data.actor,data.actor_mem⟩))
    (hfactor : IsSL2Two
      (⁅SectionOne.oddCore K,Subgroup.zpowers (f ⟨data.actor,data.actor_mem⟩)⁆ ⊔
        Subgroup.zpowers (f ⟨data.actor,data.actor_mem⟩) : Subgroup K)) :
    let U := QAt ctx.Γ ctx.criticalPath.firstStep
    let N := QAt ctx.Γ ctx.criticalPath.a ⊓ U
    let R := QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote)
    let F := R ⊔ Subgroup.zpowers data.actor
    let C := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
    ∀ hN : (C.subgroupOf U).Normal,
      let _ := hN
      ∀ (_hW : IsElementaryAbelian 2 (U ⧸ C.subgroupOf U)),
        Nat.card (U ⧸ C.subgroupOf U) = 4 →
        ∀ (action : F →* MulAut (U ⧸ C.subgroupOf U)),
          (∀ mover : F, ∀ point : U,
            ∃ hconj : (mover : G)*(point : G)*(mover : G)⁻¹ ∈ U,
              action mover (QuotientGroup.mk' (C.subgroupOf U) point) =
                QuotientGroup.mk' (C.subgroupOf U)
                  ⟨(mover : G)*(point : G)*(mover : G)⁻¹,hconj⟩) →
          IsSL2Two action.range := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let U := QAt Γ cp.firstStep
  let N := QAt Γ cp.a ⊓ U
  let d := Γ.act data.conjugator data.remote
  let R := QAt Γ cp.a ⊓ QAt Γ d
  let F := R ⊔ Subgroup.zpowers data.actor
  let C := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
  let t : P := ⟨data.actor,data.actor_mem⟩
  let x : P := ⟨data.conjugator,nine_four_conjugator_mem_stabilizer Γ cp.firstStep
    data.actor data.conjugator data.actor_mem data.conjugator_mem⟩
  let u : P := x⁻¹*t*x
  let D := ⁅SectionOne.oddCore K,Subgroup.zpowers (f t)⁆ ⊔ Subgroup.zpowers (f t)
  let Fbar := (F.subgroupOf P).map f
  dsimp only
  intro hN
  let _ := hN
  intro hW hcard action hact
  let _ := hW
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
  obtain ⟨σ,_hσsurj,hcompat⟩ :=
    Subgroup.quotient_conjugation_image_descent P F U C hFP hFU f hker hN
      hW.toIsMulCommutative action hact'
  have hgen := data.generates cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    ((mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote)))
  have hDimage : D ≤ Fbar := (nine_four_factor_le_auxiliary_image ctx hb
    data.remote data.distance data.actor ⟨data.actor_mem,data.actor_centralizes⟩
    data.conjugator data.conjugator_mem hremote hne hgen f hsurj hkernel
    hinvolution hfactor).1
  have hxD : f x ∈ D := by
    have hEP : EAt Γ cp.firstStep ≤ P := by
      change Γ.twoResidualAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
      rw [Γ.twoResidualAt_def]
      exact twoResidualIn_le _
    have htP : Subgroup.zpowers data.actor ≤ P := Subgroup.zpowers_le.mpr data.actor_mem
    have hnative : (⁅EAt Γ cp.firstStep,Subgroup.zpowers data.actor⁆).subgroupOf P =
        ⁅(EAt Γ cp.firstStep).subgroupOf P,Subgroup.zpowers t⁆ := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup _ _).trans
        (sup_le hEP htP)),Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hEP,
        MonoidHom.map_zpowers]
      rfl
    have hxnative : x ∈ ⁅(EAt Γ cp.firstStep).subgroupOf P,Subgroup.zpowers t⁆ := by
      rw [← hnative]
      exact data.conjugator_mem
    have hodd := nine_local_residual_image_le_oddCore ctx.toLocalContext cp.firstStep cp.a
      (Γ.adjacent_symm cp.firstStep_adj) f hsurj hkernel.symm.le
    apply (le_sup_left : ⁅SectionOne.oddCore K,Subgroup.zpowers (f t)⁆ ≤ D)
    have hmap := Subgroup.mem_map_of_mem f hxnative
    rw [Subgroup.map_commutator,MonoidHom.map_zpowers] at hmap
    exact Subgroup.commutator_mono hodd le_rfl hmap
  have huR : (u:G) ∈ R := by
    apply nine_four_actor_closure_le_core_intersection ctx hb data.remote data.distance
      data.actor ⟨data.actor_mem,data.actor_centralizes⟩ data.conjugator
      data.conjugator_mem hremote hne
    apply Subgroup.subset_closure
    refine ⟨1,⟨data.conjugator⁻¹*data.actor*data.conjugator,Subgroup.mem_zpowers _⟩,?_⟩
    simp [u,x,t]
  let tF : F := ⟨data.actor,Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
  let uF : F := ⟨u,Subgroup.mem_sup_left huR⟩
  have hCN : C ≤ N := by
    have h := iInf_le (fun mover : F => N.map (MulAut.conj (mover:G)).toMonoidHom) 1
    have hi : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by
      ext g
      simp
    simpa only [OneMemClass.coe_one,hi,Subgroup.map_id] using h
  let q := QuotientGroup.mk' (C.subgroupOf U)
  let Bq := (N.subgroupOf U).map q
  have hBlift : (Bq.comap q).map U.subtype = N := by
    have hqker : q.ker ≤ N.subgroupOf U := by
      rw [QuotientGroup.ker_mk']
      exact Subgroup.subgroupOf_mono U hCN
    have hcomap : Bq.comap q = N.subgroupOf U := by
      exact Subgroup.comap_map_eq_self hqker
    rw [hcomap]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have htNotNormal : data.actor ∉ Subgroup.normalizer N :=
    (nine_four_central_actor_geometry ctx hb data.actor data.actor_mem hgen data.displacement).2
  have huNormal : (uF:G) ∈ Subgroup.normalizer N :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(QAt Γ cp.a).le_normalizer huR.1,
        stabilizer_le_normalizer_q Γ cp.firstStep u.property⟩
  have huB : Bq.map (action uF).toMonoidHom = Bq :=
    action_preserves_quotient_image_of_normalizer F U C N hFU hCN inf_le_right
      action hact' uF huNormal
  have hneq : action tF ≠ action uF :=
    action_ne_of_support_normalizer_contrast F U C N hFU Bq action hact'
      hBlift tF uF htNotNormal huB
  have hneone : action tF ≠ 1 := by
    have honeB : Bq.map (action 1).toMonoidHom = Bq := by
      rw [action.map_one]
      change Bq.map (MonoidHom.id _) = Bq
      exact Subgroup.map_id Bq
    simpa only [map_one] using
      (action_ne_of_support_normalizer_contrast F U C N hFU Bq action hact'
        hBlift tF 1 htNotNormal honeB)
  let tb : Fbar := ⟨f t,Subgroup.mem_map_of_mem f tF.property⟩
  let ub : Fbar := ⟨f u,Subgroup.mem_map_of_mem f uF.property⟩
  let xb : Fbar := ⟨f x,hDimage hxD⟩
  have htb : σ tb = action.rangeRestrict tF := hcompat tF
  have hub : σ ub = action.rangeRestrict uF := hcompat uF
  have hconjugate : ub = xb⁻¹*tb*xb := by
    apply Subtype.ext
    simp only [ub,xb,tb,u,map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv]
  have htbSquare : tb^2 = 1 := Subtype.ext hinvolution.2
  have htImage : _root_.IsInvolution (action.rangeRestrict tF) := by
    refine ⟨fun h => hneone (congrArg Subtype.val h),?_⟩
    rw [← htb,← map_pow,htbSquare,map_one]
  have huImage : _root_.IsInvolution (action.rangeRestrict uF) := by
    have hc : action.rangeRestrict uF = (σ xb)⁻¹*action.rangeRestrict tF*σ xb := by
      rw [← hub,hconjugate,map_mul,map_mul,map_inv,htb]
    rw [hc]
    refine ⟨?_,?_⟩
    · intro hone
      apply htImage.1
      have h := congrArg (fun z => σ xb*z*(σ xb)⁻¹) hone
      simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_one,mul_inv_cancel] using h
    · have h := congrArg (fun z => (σ xb)⁻¹*z*σ xb) htImage.2
      simpa only [pow_two,mul_assoc,mul_inv_cancel_left,mul_one,inv_mul_cancel] using h
  let _ := MulDistribMulAction.compHom (U ⧸ C.subgroupOf U) action
  exact action_range_isSL2Two_of_distinct_involutions action hcard tF uF htImage huImage
    (fun h => hneq (congrArg Subtype.val h))

end Stellmacher.SectionNine
