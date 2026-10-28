module
public import Stellmacher.SectionNine.DistanceOneCenterResidual
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineResidualImageOddCore
public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import Theory.GroupAction.CoprimeHall
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore
public import Stellmacher.SectionFiveToSeven.ResidualTransport

/-!
# Core-fixed vectors in the next residual module

For an actual ambient Section Nine critical path of length greater than
one, at every vertex in the first-step orbit, the part of [V,E] centralizing
the local two-core Q lies in the vertex center Z. No local quotient model,
module order, or fixed-subgroup identity is assumed.

At the first vertex, V lies in Q, so a Q-fixed vector in [V,E] belongs to
the center of Q. The length-independent core-center residual theorem makes
it E-fixed. In the literal quotient V/Z, the residual has odd image because
the conjugation action kills Q. Coprime fixed-point/commutator decomposition
then makes the image of this vector trivial: it lies both in the fixed
subgroup and in the exact image of [V,E]. The original vector therefore
lies in Z. The supplied vertex conjugation transports this bound to the
entire first-step orbit, retaining the ambient subgroup definitions.

This is the upper inclusion in the residual-module fixed-subgroup identity
used in the central case of Stellmacher (9.4), printed p.52/PDF p.42 of
`refs/files/stellmacher-n-group.pdf`. The separate center-in-residual result
supplies the reverse inclusion required by the identity's consumer.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u

private theorem first_residual_core_fixed_le_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep,EAt ctx.Γ ctx.criticalPath.firstStep⁆ ⊓
      Subgroup.centralizer (QAt ctx.Γ ctx.criticalPath.firstStep : Set G) ≤
        ZAt ctx.Γ ctx.criticalPath.firstStep := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Q := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let D := ⁅V,E⁆
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ cp.firstStep
  have hEP : E ≤ P := by
    change Γ.twoResidualAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hDV : D ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hEP.trans hPV)
  have hVQ : V ≤ Q := neighbor_join_le_core_of_length_gt_one Γ cp hb cp.firstStep
  have hcenterResidual : ⁅(Subgroup.center Q).map Q.subtype,E⁆ = ⊥ := by
    simpa only [Q,E,QAt,EAt,CosetGraphContext.e,CosetGraphContext.stabilizer,Γ.twoResidualAt_def] using
      next_core_center_residual ctx.sectionSeven Γ cp ctx.commutator_eq
  obtain ⟨hN,hW,action,haction,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx hb cp.firstStep ⟨1,Γ.act_one _⟩
  let _ := hN
  let _ := hW
  let W := V ⧸ Z.subgroupOf V
  let projection := QuotientGroup.mk' (Z.subgroupOf V)
  let F := (E.subgroupOf P).map action
  let X := action.range
  let internal := (E.subgroupOf P).map action.rangeRestrict
  have hinternalOdd : internal ≤ SectionOne.oddCore X :=
    nine_local_residual_image_le_oddCore ctx.toLocalContext cp.firstStep cp.a
      (Γ.adjacent_symm cp.firstStep_adj) action.rangeRestrict action.rangeRestrict_surjective
      (by
        change pCore 2 P ≤ action.rangeRestrict.ker
        rw [MonoidHom.ker_rangeRestrict,hkernel])
  have hmapInternal : internal.map action.range.subtype = F := by
    rw [Subgroup.map_map]
    rfl
  have hFcop : Nat.Coprime 2 (Nat.card F) := by
    rw [← hmapInternal,Subgroup.card_map_of_injective action.range.subtype_injective]
    exact (pPrimeCore_coprime_card (p := 2) (G := X)).of_dvd_right
      (Subgroup.card_dvd_of_le hinternalOdd)
  have hcop : Nat.Coprime (Nat.card F) (Nat.card W) := by
    obtain ⟨power,hpower⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hpower]
    exact hFcop.symm.pow_right power
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := F) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  have hImage := Subgroup.quotient_conjugation_commutatorAction_eq_image P V Z E
    hPV hEP hN action haction
  intro point hpoint
  have hpointV := hDV hpoint.1
  let vector : V := ⟨point,hpointV⟩
  have hpointCenter : point ∈ (Subgroup.center Q).map Q.subtype := by
    refine ⟨⟨point,hVQ hpointV⟩,?_,rfl⟩
    exact Subgroup.mem_center_iff.mpr fun actor => Subtype.ext (hpoint.2 actor actor.property)
  have hpointE : point ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcenterResidual hpointCenter
  have hfixed : projection vector ∈ fixedPointSubgroup F W := by
    intro actor
    obtain ⟨lift,hlift,hEq⟩ := actor.property
    change (actor : MulAut W) (projection vector) = projection vector
    rw [← hEq,haction]
    congr 1
    apply Subtype.ext
    change (lift:G) * point * (lift:G)⁻¹ = point
    rw [hpointE lift hlift,mul_inv_cancel_right]
  have hdisplacement : projection vector ∈ commutatorAction F W := by
    rw [hImage]
    exact Subgroup.mem_map_of_mem projection hpoint.1
  have hidentity : projection vector = 1 := hcompl.disjoint.le_bot ⟨hfixed,hdisplacement⟩
  exact (QuotientGroup.eq_one_iff vector).mp hidentity

public theorem nine_next_residual_core_fixed_le_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex) :
    ⁅VAt ctx.Γ vertex,EAt ctx.Γ vertex⁆ ⊓
      Subgroup.centralizer (QAt ctx.Γ vertex : Set G) ≤ ZAt ctx.Γ vertex := by
  obtain ⟨actor,hactor⟩ := horbit
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let equiv := MulAut.conj actor
  have hback : Γ.act actor⁻¹ vertex = cp.firstStep := by
    rw [← hactor,← Γ.act_mul,mul_inv_cancel,Γ.act_one]
  have hVmap : (VAt Γ vertex).map equiv.toMonoidHom = VAt Γ cp.firstStep := by
    have hh := v_act Γ actor⁻¹ vertex
    simpa only [inv_inv,hback] using hh.symm
  have hQmap : (QAt Γ vertex).map equiv.toMonoidHom = QAt Γ cp.firstStep := by
    have hh := q_act Γ actor⁻¹ vertex
    simpa only [inv_inv,hback] using hh.symm
  have hZmap : (ZAt Γ vertex).map equiv.toMonoidHom = ZAt Γ cp.firstStep := by
    have hh := z_act Γ actor⁻¹ vertex
    simpa only [inv_inv,hback] using hh.symm
  have hEmap : (EAt Γ vertex).map equiv.toMonoidHom = EAt Γ cp.firstStep := by
    change (Γ.twoResidualAt vertex).map equiv.toMonoidHom = Γ.twoResidualAt cp.firstStep
    rw [Γ.twoResidualAt_def,Γ.twoResidualAt_def,← twoResidualIn_map_equiv]
    change twoResidualIn (conjugateBy (stabilizer Γ vertex) actor) =
      twoResidualIn (stabilizer Γ cp.firstStep)
    have hh := stabilizer_act Γ actor⁻¹ vertex
    simpa only [inv_inv,hback] using congrArg twoResidualIn hh.symm
  apply (Subgroup.map_le_map_iff_of_injective (f := equiv.toMonoidHom) equiv.injective).mp
  rw [hZmap]
  apply le_trans ?_ (first_residual_core_fixed_le_center ctx hb)
  apply le_inf
  · have hh := Subgroup.map_mono (f := equiv.toMonoidHom)
      (inf_le_left : ⁅VAt Γ vertex,EAt Γ vertex⁆ ⊓
        Subgroup.centralizer (QAt Γ vertex : Set G) ≤ ⁅VAt Γ vertex,EAt Γ vertex⁆)
    rw [Subgroup.map_commutator,hVmap,hEmap] at hh
    exact hh
  · have hh := (Subgroup.map_mono (f := equiv.toMonoidHom)
      (inf_le_right : ⁅VAt Γ vertex,EAt Γ vertex⁆ ⊓
        Subgroup.centralizer (QAt Γ vertex : Set G) ≤
          Subgroup.centralizer (QAt Γ vertex : Set G))).trans
      (Subgroup.map_centralizer_le_centralizer_image (QAt Γ vertex : Set G) equiv.toMonoidHom)
    change _ ≤ Subgroup.centralizer ((QAt Γ vertex).map equiv.toMonoidHom : Set G) at hh
    rwa [hQmap] at hh

end Stellmacher.SectionNine
