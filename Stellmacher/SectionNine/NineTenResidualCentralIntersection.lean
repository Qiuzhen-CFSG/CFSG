module
public import Stellmacher.SectionNine.NineTenPrescribedActorGeometry
public import Stellmacher.SectionNine.NineTenPrescribedFirstTransvection
public import Stellmacher.SectionNine.NineTenCommonNeighborGeneration
public import Stellmacher.SectionNine.LemmaNineFour

/-!
# Residual-central subgroups meet the predecessor in the first module

Retain the actual two extraction packets from the long-distance proof of
Stellmacher (9.10). If a subgroup C centralizes the first residual modulo
the first module, its intersection with the extracted predecessor module
lies in the first module. This proves the implication used in assertion
(11), printed p.59 of `refs/files/stellmacher-n-group.pdf`, for the source's
largest normal subgroup C. Neither its extra normality nor its neighborhood
containment is needed by this argument.

The prescribed inverse conjugator belongs to the first residual. An element
of C therefore differs from its conjugate by an element of the first
module. If it also lies in the predecessor module, that conjugate lies in
the third module, which the same prescribed actor centralizes. The first
module is actor-invariant, so the intersection's actor commutator lies in
it. Apply the genuine ambient (9.4) with that same actor, inverse conjugator,
actual common-neighbor generation and the first extraction's index-two
transvection displacement. No later (9.10) conclusion is assumed.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u
public theorem nine_ten_residual_central_predecessor_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hactorNeighbor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorComm : twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (firstActor : G) (firstE firstA0 : Subgroup G)
    (firstData : NineThreeGeometricData ctx.Γ ctx.criticalPath.a'
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
      (VAt ctx.Γ ctx.criticalPath.firstStep) firstE firstA0 firstActor)
    (hfirstNew : ctx.Γ.act firstData.x⁻¹
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) =
        neighbor)
    (C : Subgroup G)
    (hCE : ⁅C,EAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep) :
    C ⊓ VAt ctx.Γ (ctx.Γ.act data.x⁻¹ (ctx.criticalPath.path ⟨3, by omega⟩)) ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 3 < cp.length := hb
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let F := EAt Γ cp.firstStep
  let third := cp.path ⟨3,by omega⟩
  let predecessor := Γ.act data.x⁻¹ third
  let I := C ⊓ VAt Γ predecessor
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hthird : IsCriticalPathOffset Γ cp 3 third := ⟨⟨3,by omega⟩,rfl,rfl⟩
  obtain ⟨hdistance,hactorGeometry,hactorNotCore,hxComm,_⟩ :=
    nine_ten_prescribed_actor_geometry ctx.toLocalContext third second neighbor
      hthird hneighbor actor E A0 data hactorNeighbor hactorComm
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ cp.firstStep
  have hFP : F ≤ P := by
    change Γ.twoResidualAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le P
  have hPF : P ≤ Subgroup.normalizer (F : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFP).mp (by
      change ((Γ.twoResidualAt cp.firstStep).subgroupOf P).Normal
      rw [Γ.twoResidualAt_def]
      exact twoResidualIn_normal P)
  have hxF : data.x⁻¹ ∈ F :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr hactorGeometry.1).trans hPF)) hxComm
  have hpredV : VAt Γ predecessor =
      (VAt Γ third).map (MulAut.conj data.x).toMonoidHom := by
    change v Γ (Γ.act data.x⁻¹ third) = _
    rw [v_act,inv_inv]
  have hMcentral : ⁅VAt Γ third,Subgroup.zpowers actor⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hactorGeometry.2))
  have hVcomm : ⁅V,Subgroup.zpowers actor⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr hactorGeometry.1).trans hPV)
  have hcomm : ⁅I,Subgroup.zpowers actor⁆ ≤ V := by
    apply Subgroup.commutator_le.mpr
    intro c hc t ht
    have hcPred : c ∈ VAt Γ predecessor := hc.2
    rw [hpredV] at hcPred
    obtain ⟨w,hw,heq⟩ := hcPred
    change data.x * w * data.x⁻¹ = c at heq
    let v := data.x⁻¹ * c * data.x
    have hv : v ∈ VAt Γ third := by
      dsimp [v]
      rw [← heq]
      simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one,SetLike.mem_coe] using hw
    let d := ⁅data.x⁻¹,c⁆
    have hd : d ∈ V := (Subgroup.commutator_comm C F ▸ hCE)
      (Subgroup.commutator_mem_commutator hxF hc.1)
    have hfactor : c = d⁻¹ * v := by
      dsimp [d,v]
      simp only [commutatorElement_def]
      group
    have hzero : ⁅v,t⁆ = 1 := Subgroup.mem_bot.mp
      (hMcentral.le (Subgroup.commutator_mem_commutator hv ht))
    rw [hfactor,commutatorElement_mul_left_eq_conj_mul,hzero]
    simp only [mul_one,mul_inv_cancel,one_mul]
    exact hVcomm (Subgroup.commutator_mem_commutator (V.inv_mem hd) ht)
  have hindex : QuotientCardEq (VAt Γ cp.firstStep)
      (VAt Γ cp.firstStep ⊓ GAt Γ neighbor) 2 := by
    change Nat.card (VAt Γ cp.firstStep) =
      2 * Nat.card (VAt Γ cp.firstStep ⊓ GAt Γ neighbor : Subgroup G)
    rw [← hfirstNew,← firstData.coatom_eq]
    exact firstData.coatom_card
  have hdisplacement := (nine_ten_prescribed_actor_first_transvection ctx hshort hterminalNot
    neighbor hneighbor hindex actor hactorNeighbor hactorNotCore).2
  have hgeneration : ∀ n : Γ.Vertex,
      n ∈ Neighborhood Γ cp.firstStep → n ∈ Neighborhood Γ predecessor →
      (GAt Γ cp.firstStep ⊓ GAt Γ n) ⊔ Subgroup.zpowers actor = GAt Γ cp.firstStep :=
    nine_ten_prescribed_actor_common_neighbor_generation ctx.toLocalContext third second neighbor
      hthird hneighbor actor E A0 data hactorNeighbor
  exact lemma_nine_four_ambient ctx hshort third hdistance actor hactorGeometry
    data.x⁻¹ hxComm I inf_le_right hcomm hgeneration hdisplacement

end Stellmacher.SectionNine
