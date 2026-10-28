module
public import Stellmacher.SectionTen.TenOneResidualActionSaturation
public import Stellmacher.SectionTen.TenOneSmallModuleResidualCore
public import Stellmacher.SectionTen.TenOneSmallCoreNeighborhoodLine
public import Theory.GroupAction.NormalizingFixedPoints

/-!
# The elementary residual quotient in the small branch

For the actual small-module Section Ten configuration, the first residual
core modulo its neighbor module is elementary abelian. The theorem retains
the normality proof for that literal quotient, and proves that the first
core acts trivially on it. Thus the stabilizer action factors through its
specified SL2(2) core quotient.

In the residual quotient the neighborhood commutator has order two. The
first core normalizes both defining groups, hence fixes this line pointwise.
Its fixed subgroup is central because the residual core is contained in
the first core. The involutions in this fixed subgroup form an invariant
subgroup. Its pullback contains the neighborhood commutator, so the actual
residual-action saturation theorem makes the pullback the whole core.
Consequently the whole quotient consists of central involutions fixed by
the first core.

This proves the elementary and action-kernel inputs to the order-four
quotient calculation in Stellmacher (10.1)(a), Journal of Algebra 190 (1997),
printed p.60. No quotient order or prescribed module structure is assumed.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u

private theorem fixed_of_card_two_invariant
    {W : Type*} [Group W] (L : Subgroup W) (hcard : Nat.card L = 2)
    (actor : MulAut W) (hstable : ∀ point ∈ L, actor point ∈ L) :
    ∀ point ∈ L, actor point = point := by
  obtain ⟨nontrivial, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : L)).mp hcard
  intro point hpoint
  by_cases hone : point = 1
  · simp [hone]
  have himage : actor point ≠ 1 := fun heq => hone (actor.injective (heq.trans actor.map_one.symm))
  have h1 := huniq (⟨point, hpoint⟩ : L) (fun h => hone (congrArg Subtype.val h))
  have h2 := huniq (⟨actor point, hstable point hpoint⟩ : L)
    (fun h => himage (congrArg Subtype.val h))
  exact congrArg Subtype.val (h2.trans h1.symm)

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_residual_quotient_elementary
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ∃ hN : ((VAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep))).Normal,
      let _ := hN
      IsElementaryAbelian 2 ((twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) ⧸
        (VAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
          (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep))) ∧
      ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep),
        QAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  let vertex := ctx.criticalPath.firstStep
  let P := GAt ctx.Γ vertex
  let Q := QAt ctx.Γ vertex
  let E := EAt ctx.Γ vertex
  let R := twoCoreIn E
  let V := VAt ctx.Γ vertex
  let U := GeneratedNeighborhoodV ctx.Γ middle
  let C := ⁅R, U⁆
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRQ : R ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt vertex) ≤ ctx.Γ.twoCoreAt vertex
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hQP : Q ≤ P := by
    change ctx.Γ.twoCoreAt vertex ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hRP := hRQ.trans hQP
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v ctx.Γ vertex
  have hVR : V ≤ R := ten_one_small_module_le_residual_core ctx middle hpath hsmall hmodel
  have hN : (V.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVR).mpr (hRP.trans hPV)
  let _ := hN
  let W := R ⧸ V.subgroupOf R
  let quotient : R →* W := QuotientGroup.mk' (V.subgroupOf R)
  obtain ⟨action, haction⟩ := Subgroup.exists_quotient_conjugation_action P R V hPR hPV hN
  obtain ⟨_, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hUcore : U ≤ QAt ctx.Γ middle :=
    nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle
  have hUP : U ≤ P := hUcore.trans
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle vertex
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2)
  have hQU : Q ≤ Subgroup.normalizer (U : Set G) :=
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core vertex middle
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst)) default).2.2).trans
        (nine_seven_stabilizer_normalizes_neighborhood ctx.Γ middle)
  have hCR : C ≤ R :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hUP.trans hPR)
  have hQC : Q ≤ Subgroup.normalizer (C : Set G) := by
    intro actor hactor
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hRmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPR (hQP hactor))
    have hUmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQU hactor)
    change R.map (MulAut.conj actor).toMonoidHom = R at hRmap
    change U.map (MulAut.conj actor).toMonoidHom = U at hUmap
    change (⁅R, U⁆).map (MulAut.conj actor).toMonoidHom = ⁅R, U⁆
    rw [Subgroup.map_commutator, hRmap, hUmap]
  let L := (C.subgroupOf R).map quotient
  have hLcard : Nat.card L = 2 := by
    change Nat.card ((C.subgroupOf R).map (QuotientGroup.mk' (V.subgroupOf R))) = 2
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hCR]
    exact ten_one_small_core_neighborhood_line ctx middle hpath hsmall hmodel
  let Qimage := (Q.subgroupOf P).map action
  let F := FixedPoints.subgroup Qimage W
  have hLfixed : L ≤ F := by
    intro point hpoint actor
    obtain ⟨actorP, hactorP, heq⟩ := actor.property
    apply fixed_of_card_two_invariant L hLcard (actor : MulAut W) ?_ point hpoint
    intro vector hvector
    obtain ⟨vectorR, hvectorR, rfl⟩ := hvector
    change (actor : MulAut W) (quotient vectorR) ∈ L
    rw [← heq, haction]
    exact Subgroup.mem_map_of_mem quotient
      ((Subgroup.mem_normalizer_iff.mp (hQC hactorP) vectorR).mp hvectorR)
  have hFcenter : F ≤ Subgroup.center W := by
    intro point hpoint
    rw [Subgroup.mem_center_iff]
    intro vector
    obtain ⟨pointR, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf R) point
    obtain ⟨vectorR, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf R) vector
    let actorP : P := ⟨vectorR, hRP vectorR.property⟩
    let actorQ : Qimage := ⟨action actorP, Subgroup.mem_map_of_mem action (hRQ vectorR.property)⟩
    have hfix := hpoint actorQ
    change action actorP (quotient pointR) = quotient pointR at hfix
    rw [haction] at hfix
    have heq : quotient vectorR * quotient pointR * (quotient vectorR)⁻¹ = quotient pointR := by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact hfix
    exact mul_inv_eq_iff_eq_mul.mp heq
  let _ : (Q.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (stabilizer_le_normalizer_q ctx.Γ vertex)
  have hAcore : action.range ≤ Subgroup.normalizer (Qimage : Set (MulAut W)) := by
    have h := (Q.subgroupOf P).le_normalizer_map action
    rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map] at h
    exact h
  let _ : IsInvariant action.range W F :=
    fixedPoints_isInvariant_of_normalizing_actor action.range Qimage hAcore
  let M : Subgroup W := {
    carrier := {point | point ∈ F ∧ point ^ 2 = 1}
    one_mem' := ⟨F.one_mem, by simp⟩
    mul_mem' := by
      rintro left right ⟨hleft, hleft2⟩ ⟨hright, hright2⟩
      refine ⟨F.mul_mem hleft hright, ?_⟩
      have hcomm : Commute left right := (Subgroup.mem_center_iff.mp (hFcenter hright)) left
      rw [hcomm.mul_pow, hleft2, hright2, one_mul]
    inv_mem' := by
      rintro point ⟨hpoint, hpoint2⟩
      refine ⟨F.inv_mem hpoint, ?_⟩
      rw [inv_pow, hpoint2, inv_one] }
  have hMforward (actor : action.range) (point : W) (hpoint : point ∈ M) :
      actor • point ∈ M := by
    refine ⟨(IsInvariant.invariant (A := action.range) (G := W) (H := F) actor point).mp hpoint.1, ?_⟩
    change ((actor : MulAut W) point) ^ 2 = 1
    rw [← map_pow, hpoint.2, map_one]
  have hLM : L ≤ M := by
    intro point hpoint
    refine ⟨hLfixed hpoint, ?_⟩
    have hpow := pow_card_eq_one' (x := (⟨point, hpoint⟩ : L))
    rw [hLcard] at hpow
    exact congrArg Subtype.val hpow
  let K := (M.comap quotient).map R.subtype
  have hPK : P ≤ Subgroup.normalizer (K : Set G) := by
    apply subgroup_le_normalizer_of_conj_mem
    intro actor point hpoint
    obtain ⟨pointR, hpointR, rfl⟩ := hpoint
    refine ⟨⟨(actor : G) * (pointR : G) * (actor : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hPR actor.property) pointR).mp pointR.property⟩, ?_, rfl⟩
    change quotient _ ∈ M
    rw [← haction]
    exact hMforward ⟨action actor, ⟨actor, rfl⟩⟩ (quotient pointR) hpointR
  have hCK : C ≤ K := by
    intro point hpoint
    refine ⟨⟨point, hCR hpoint⟩, ?_, rfl⟩
    exact hLM (Subgroup.mem_map_of_mem quotient hpoint)
  have hRK : R ≤ K := ten_one_residual_action_saturation ctx middle hpath hmodel K hPK hCK
  have hMtop : M = ⊤ := by
    apply top_unique
    intro point _
    obtain ⟨pointR, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf R) point
    obtain ⟨otherR, hotherR, heq⟩ := hRK pointR.property
    have heqR : otherR = pointR := Subtype.ext heq
    exact heqR ▸ hotherR
  refine ⟨hN, ?_, ?_⟩
  · change IsElementaryAbelian 2 W
    refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · intro left right
      exact (Subgroup.mem_center_iff.mp (hFcenter (hMtop.ge (Subgroup.mem_top right)).1)) left
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro point
      exact (hMtop.ge (Subgroup.mem_top point)).2
  · change ⁅R, Q⁆ ≤ V
    rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro actor hactor vector hvector
    let actorP : P := ⟨actor, hQP hactor⟩
    let vectorR : R := ⟨vector, hvector⟩
    have hfixed := (hMtop.ge (Subgroup.mem_top (quotient vectorR))).1
    have hfix := hfixed ⟨action actorP, Subgroup.mem_map_of_mem action hactor⟩
    change action actorP (quotient vectorR) = quotient vectorR at hfix
    rw [haction] at hfix
    have hmem := QuotientGroup.eq_iff_div_mem.mp hfix
    change actor * vector * actor⁻¹ / vector ∈ V at hmem
    simpa only [commutatorElement_def, div_eq_mul_inv] using hmem
end Stellmacher.SectionTen

