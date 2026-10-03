module
public import Stellmacher.SectionTen.TenOneLargeGeneratedResidualSaturation
public import Stellmacher.SectionTen.TenOneLargeNeighborhoodAction
public import Stellmacher.SectionTen.TenOneGeneratedElementary
public import Theory.GroupAction.NormalizingFixedPoints

/-!
# The elementary terminal residual quotient in the large branch

For the actual no-transvection Section Ten context, the terminal residual
two-core U modulo the terminal module V is elementary abelian, and the
terminal two-core Q acts trivially on this literal quotient. The normality
witness is retained with the quotient and its elementary instance.

Source (17) puts [W,Q] in V, so the actual image of the elementary subgroup W
is fixed pointwise by Q. In U/V the Q-fixed subgroup is central, since U≤Q.
Its involutions form a subgroup invariant under the terminal stabilizer.
The pullback contains W and is stabilizer-normal, so the generated-residual
saturation theorem makes it the whole U. This proves both elementary
abelianness and the exact core commutator bound.

This is the structural step in Stellmacher (10.1)(18), printed p.64 of
`refs/files/stellmacher-n-group.pdf`. No cardinality of U/V, irreducible
quotient model or desired generation conclusion is assumed.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_residual_quotient_elementary
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ∃ hN : ((VAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'))).Normal,
      let _ := hN
      IsElementaryAbelian 2 (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ⧸
        (VAt ctx.Γ ctx.criticalPath.a').subgroupOf (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'))) ∧
      ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'), QAt ctx.Γ ctx.criticalPath.a'⁆ ≤
        VAt ctx.Γ ctx.criticalPath.a' := by
  have hedge := (ten_one_large_neighborhood_action ctx middle hpath hno).2
  let vertex := ctx.criticalPath.a'
  let P := GAt ctx.Γ vertex
  let Q := QAt ctx.Γ vertex
  let E := EAt ctx.Γ vertex
  let R := twoCoreIn E
  let V := VAt ctx.Γ vertex
  let WW := conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ vertex)
    (GAt ctx.Γ middle)
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
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hVQ : V ≤ Q := neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hshort vertex
  have hVfull : ⁅V,E⁆=V := ten_one_large_terminal_residual_full ctx middle hpath hno
  have hVR : V ≤ R := by
    rw [←hVfull,Subgroup.commutator_comm]
    apply le_trans (Subgroup.commutator_mono le_rfl hVQ)
    change ⁅E,ctx.Γ.twoCoreAt vertex⁆ ≤ twoCoreIn E
    rw [hE,ctx.Γ.twoCoreAt_def]
    exact residual_commutator_core_le P
  have hN : (V.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVR).mpr (hRP.trans hPV)
  let _ := hN
  let W := R ⧸ V.subgroupOf R
  let quotient : R →* W := QuotientGroup.mk' (V.subgroupOf R)
  obtain ⟨action,haction⟩ := Subgroup.exists_quotient_conjugation_action P R V hPR hPV hN
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hQmiddle : Q ≤ GAt ctx.Γ middle :=
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core vertex middle
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) default).2.2)
  have hWQ : ⁅WW,Q⁆ ≤ V :=
    (Subgroup.commutator_mono le_rfl (le_inf hQmiddle hQP)).trans hedge
  have hWR : WW ≤ R := (ten_one_large_first_residual_index ctx middle hpath hno).2
  have hW : IsElementaryAbelian 2 WW := ten_one_generated_elementary ctx middle hpath
  let _ := hW
  let L := (WW.subgroupOf R).map quotient
  let Qimage := (Q.subgroupOf P).map action
  let F := FixedPoints.subgroup Qimage W
  have hLfixed : L ≤ F := by
    rintro point ⟨source,hsource,rfl⟩ actor
    obtain ⟨actorP,hactorP,heq⟩ := actor.property
    change (actor:MulAut W) (quotient source)=quotient source
    rw [←heq,haction]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hc : ⁅(actorP:G),(source:G)⁆ ∈ V := by
      rw [←commutatorElement_inv]
      exact V.inv_mem (hWQ (Subgroup.commutator_mem_commutator hsource hactorP))
    change (actorP:G) * (source:G) * (actorP:G)⁻¹ / (source:G) ∈ V
    simpa only [commutatorElement_def,div_eq_mul_inv] using hc
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
    rintro point ⟨source,hsource,rfl⟩
    refine ⟨hLfixed (Subgroup.mem_map_of_mem quotient hsource), ?_⟩
    rw [← map_pow]
    have hp : source ^ 2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (A:=WW) (source:G) (show (source:G)∈WW from hsource)
    rw [hp,map_one]
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
  have hCK : WW ≤ K := by
    intro point hpoint
    refine ⟨⟨point, hWR hpoint⟩, ?_, rfl⟩
    exact hLM (Subgroup.mem_map_of_mem quotient hpoint)
  have hRK : R ≤ K := ten_one_large_generated_residual_saturation ctx middle hpath hno K hPK hCK
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
