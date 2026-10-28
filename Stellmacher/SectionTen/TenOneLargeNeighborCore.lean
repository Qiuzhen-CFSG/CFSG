module
public import Stellmacher.SectionTen.TenOneGeneratedQuotient
public import Theory.GroupTheory.C5C4ElementaryTwoSubgroup

/-!
# Neighbor-core index two from the Frobenius quotient

In the standing Section Ten geometry, source (19)'s Frobenius20 quotient at
the first neighbor forces every middle-neighbor core to have relative index
two in the actual generated neighborhood Wnext. The first quotient model is
the sole additional source-case hypothesis; no core image or index is assumed.

The actual elementary quotient Wnext/W maps to the supplied C5 semidirect C4
model because W lies in every neighboring core. Thus the actual image of
Wnext is elementary, and the generic elementary-two-subgroup bound in that
model gives order at most two. Critical module noncontainment excludes order
one. Middle-stabilizer conjugacy and covariance of the generated neighborhood
transport the first index to all three neighbors.

This is the local kernel input to the common Wnext/W₀ index computation after
(19), Stellmacher (10.1), Journal of Algebra 190 (1997), printed pp.64–65 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_neighbor_core_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hmodel : QuotientIsFrobenius20 (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep))
    {neighbor : ctx.Γ.Vertex} (hadj : ctx.Γ.adjacent middle neighbor) :
    (QAt ctx.Γ neighbor).relIndex (GeneratedNeighborhoodV ctx.Γ middle) = 2 := by
  let U := GeneratedNeighborhoodV ctx.Γ middle
  let W := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle)
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let R := QAt ctx.Γ ctx.criticalPath.firstStep
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hUQ : U ≤ QAt ctx.Γ middle :=
    nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext
      hb middle
  have hUP : U ≤ P := hUQ.trans
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2)
  have hWQ : W ≤ R := (ten_one_generated_containment ctx middle hpath).trans
    (inf_le_left.trans (sInf_le
      ⟨ctx.criticalPath.firstStep, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst, rfl⟩))
  obtain ⟨φ, _, projection, _, hprojectionKernel⟩ := hmodel
  let model := SemidirectProduct C5 C4 φ
  let f : U →* model := projection.comp (Subgroup.inclusion hUP)
  have hfkernel : f.ker = R.subgroupOf U := by
    ext x
    change projection ⟨(x : G), hUP x.property⟩ = 1 ↔ (x : G) ∈ R
    rw [← MonoidHom.mem_ker, hprojectionKernel]
    rfl
  obtain ⟨hN, hQelem⟩ := ten_one_generated_quotient_elementary ctx middle hpath
  let _ := hN
  let Q := U ⧸ W.subgroupOf U
  let _ : IsElementaryAbelian 2 Q := hQelem
  let quotient : U →* Q := QuotientGroup.mk' (W.subgroupOf U)
  have hWkernel : W.subgroupOf U ≤ f.ker := by
    rw [hfkernel]
    exact fun _ hx => hWQ hx
  let action : Q →* model := QuotientGroup.lift (W.subgroupOf U) f hWkernel
  have hrange : action.range = f.range := by
    ext point
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (W.subgroupOf U) x
      exact ⟨y, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨quotient x, rfl⟩
  have helementary : IsElementaryAbelian 2 f.range := by
    rw [← hrange]
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨point, x, rfl⟩
    apply Subtype.ext
    change (action x)^2 = 1
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 Q) x, map_one]
  have hbound := SemidirectProduct.elementary_two_subgroup_card_le_two φ f.range helementary
  have hcard := Subgroup.index_ker f
  rw [hfkernel] at hcard
  change R.relIndex U = Nat.card f.range at hcard
  have hindexBound : R.relIndex U ≤ 2 := hcard.trans_le hbound
  have hnot : ¬ U ≤ R := by
    intro hle
    exact (sectionTenOpeningData ctx middle hpath).terminal_noncontainment
      ((show VAt ctx.Γ ctx.criticalPath.a' ≤ U from
        le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal, rfl⟩).trans hle)
  have hnotone : R.relIndex U ≠ 1 := fun h => hnot (Subgroup.relIndex_eq_one.mp h)
  have hpositive : R.relIndex U ≠ 0 := (R.subgroupOf U).index_ne_zero_of_finite
  have hfirstIndex : R.relIndex U = 2 := by omega
  obtain ⟨actor, hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  have hfix : ctx.Γ.act (actor : G) middle = middle :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def middle) _).mp actor.property
  have hUmap : U.map (MulAut.conj (actor : G)⁻¹).toMonoidHom = U := by
    change (GeneratedNeighborhoodV ctx.Γ middle).map _ = _
    rw [← nine_seven_neighborhood_act, hfix]
  rw [← hmove, QAt, q_act]
  change ((QAt ctx.Γ ctx.criticalPath.firstStep).map
    (MulAut.conj (actor : G)⁻¹).toMonoidHom).relIndex U = 2
  conv_lhs => rw [← hUmap]
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj (actor : G)⁻¹).injective]
  exact hfirstIndex

end Stellmacher.SectionTen

