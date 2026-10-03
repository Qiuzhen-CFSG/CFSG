module
public import Stellmacher.SectionTen.TenOneCommonIntersection
public import Stellmacher.SectionTen.TenOneGeneratedContainment

/-!
# The elementary generated quotient in Stellmacher (10.1)

For the standing Section Ten context, the literal quotient Wnext/W is
normal and elementary abelian. Moreover [W,Wnext] lies in the middle center.
No branch cardinalities, local quotient classification, normality, or
commutator conclusions are added to the geometric hypotheses.

The common endpoint-module intersection I lies in the seed of W, since the
terminal module lies in its own core. The unconditional derived bound
Wnext'≤I therefore gives a commutative quotient and its normality. Every
neighbor module is a conjugate of the elementary first module, and their
images generate the quotient; its squaring homomorphism is consequently
trivial. For the commutator estimate, W lies in every neighbor core, so its
commutator with each neighbor module lies in that neighbor center. These
centers lie in Zmiddle, and the normalized join estimate completes the proof.

This supplies the quotient module for the common index calculation and the
large-branch refinement following (19), Stellmacher (10.1), Journal of
Algebra190 (1997), printed pp.60–65 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_common_intersection_le_generated
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex) :
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' ≤
      conjugateClosure
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ middle) := by
  intro element helement
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hcore := neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hb
    ctx.criticalPath.a'
  exact Subgroup.subset_closure ⟨1, ⟨element, helement.1, hcore helement.2⟩, by simp⟩

public theorem ten_one_generated_commutator_le_middle_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ⁅conjugateClosure
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ middle), GeneratedNeighborhoodV ctx.Γ middle⁆ ≤
      ZAt ctx.Γ middle := by
  let W := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle)
  let family : Set (Subgroup G) := {module | ∃ neighbor,
    neighbor ∈ Neighborhood ctx.Γ middle ∧ module = VAt ctx.Γ neighbor}
  obtain ⟨hmiddle, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hUQ := nine_seven_neighborhood_le_own_core
    ctx.toLocalContext.toSectionNineLocalContext hb middle
  have hQP : QAt ctx.Γ middle ≤ GAt ctx.Γ middle := by
    rw [QAt, q, ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hcontain : ∀ subgroup ∈ family, subgroup ≤ GAt ctx.Γ middle := by
    rintro subgroup ⟨neighbor, hneighbor, rfl⟩
    exact (show VAt ctx.Γ neighbor ≤ GeneratedNeighborhoodV ctx.Γ middle from
      le_sSup ⟨neighbor, hneighbor, rfl⟩).trans (hUQ.trans hQP)
  rw [Subgroup.commutator_comm]
  change ⁅sSup family, W⁆ ≤ _
  apply SectionEight.eight_six_commutator_sSup_le family W _ (GAt ctx.Γ middle)
    (stabilizer_le_normalizer_z ctx.Γ middle) hcontain
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  have hWQ : W ≤ QAt ctx.Γ neighbor :=
    (ten_one_generated_containment ctx middle hpath).trans
      (inf_le_left.trans (sInf_le ⟨neighbor, hneighbor, rfl⟩))
  obtain ⟨actor, hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) hneighbor
  have hfour := (lemma_nine_three_ambient ctx.toAmbientSectionNineContext (by omega)
    ctx.criticalPath.a ⟨1, ctx.Γ.act_one _⟩).2
  have hcomm := (nine_next_center_and_commutator_of_initial_four
    ctx.toAmbientSectionNineContext.toLocalContext hfour neighbor ⟨actor, hmove⟩).2
  exact ((Subgroup.commutator_mono le_rfl hWQ).trans_eq hcomm).trans
    ((nine_seven_center_join ctx.toAmbientSectionNineContext middle hmiddle).2
      neighbor hneighbor).2

public theorem ten_one_generated_quotient_elementary
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ∃ hN : ((conjugateClosure
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ middle)).subgroupOf (GeneratedNeighborhoodV ctx.Γ middle)).Normal,
      let _ := hN
      IsElementaryAbelian 2
        (GeneratedNeighborhoodV ctx.Γ middle ⧸ (conjugateClosure
          (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
          (GAt ctx.Γ middle)).subgroupOf (GeneratedNeighborhoodV ctx.Γ middle)) := by
  let U := GeneratedNeighborhoodV ctx.Γ middle
  let W := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle)
  have hWU : W ≤ U := (ten_one_generated_containment ctx middle hpath).trans inf_le_right
  have hderived : ⁅U, U⁆ ≤ W := by
    rw [← Subgroup.map_subtype_commutator U]
    exact (ten_one_generated_derived_le_intersection ctx middle hpath).trans
      (ten_one_common_intersection_le_generated ctx middle)
  have hN : (W.subgroupOf U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.le_normalizer_iff_commutator_le_right.mpr
        ((Subgroup.commutator_mono le_rfl hWU).trans hderived))
  let _ := hN
  let Q := U ⧸ W.subgroupOf U
  let projection : U →* Q := QuotientGroup.mk' (W.subgroupOf U)
  have hnative : commutator U ≤ W.subgroupOf U := by
    intro x hx
    exact hderived (by
      rw [← Subgroup.map_subtype_commutator U]
      exact Subgroup.mem_map_of_mem U.subtype hx)
  let _ : IsMulCommutative Q :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hnative
  let _ : CommGroup Q := IsMulCommutative.instCommGroup
  let square : Q →* Q := powMonoidHom 2
  let K := (square.ker.comap projection).map U.subtype
  obtain ⟨_, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hb).1
  have hVU {v : ctx.Γ.Vertex} (hv : v ∈ Neighborhood ctx.Γ middle) : VAt ctx.Γ v ≤ U :=
    le_sSup ⟨v, hv, rfl⟩
  have helementary (v : ctx.Γ.Vertex) (hv : v ∈ Neighborhood ctx.Γ middle) :
      IsElementaryAbelian 2 (VAt ctx.Γ v) := by
    obtain ⟨mover, hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) hv
    have hmap : VAt ctx.Γ v = (VAt ctx.Γ ctx.criticalPath.firstStep).map
        (MulAut.conj (mover : G)⁻¹).toMonoidHom := by
      rw [← hmove]
      exact v_act ctx.Γ mover ctx.criticalPath.firstStep
    rw [hmap]
    exact IsElementaryAbelian.map _
  have hUK : U ≤ K := by
    apply sSup_le
    rintro F ⟨v, hv, rfl⟩
    let _ := helementary v hv
    intro x hx
    refine ⟨⟨x, hVU hv hx⟩, ?_, rfl⟩
    change (projection ⟨x, hVU hv hx⟩)^2 = 1
    rw [← map_pow]
    have hxpow : (⟨x, hVU hv hx⟩ : U)^2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := VAt ctx.Γ v) x hx)
    rw [hxpow, map_one]
  refine ⟨hN, ?_⟩
  refine ⟨?_⟩
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro point
  obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective (W.subgroupOf U) point
  obtain ⟨x, hx, hxe⟩ := hUK element.property
  have heq : x = element := Subtype.ext hxe
  change (projection x)^2 = 1 at hx
  exact heq ▸ hx

end Stellmacher.SectionTen

