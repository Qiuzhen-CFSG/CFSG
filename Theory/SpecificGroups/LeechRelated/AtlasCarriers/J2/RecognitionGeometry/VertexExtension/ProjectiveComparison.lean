module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.Eight
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.ProjectiveComparison.Action
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.PGLComparison

/-!
# Compatible PGL₂(9) coordinates for the marked J₂ vertex quotient

Given C/X ≃ A₆ and perfectness of C, conjugation embeds the literal M/X
into Aut(A₆). The published order-eight element excludes the natural S₆
extension, so the exceptional-involution comparison gives M/X ≃ PGL₂(9).

To retain the actual inclusion, we adjust the A₆ coordinates: the image of
the perfect central quotient lies in the derived subgroup PSL₂(9), and its
order makes it the whole canonical PSL₂ image. Restricting the projective
comparison to that image gives a compatible pair of equivalences. The final
theorem retains conjugation by the literal splitter, and the quotient-map
lemma states the diagram before passing to quotient representatives.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3(1) and 47.10,
pp.261–267. The central quotient and perfectness are explicit inputs from
the independent central-cover construction. No order hypothesis on M or
additional extension-structure premise is needed.
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension
open Subgroup Equiv
open AlternatingSix.ShadowLocal AlternatingSix.OuterInvolutionExtension
open Atlas.Comparisons.Exceptional GorensteinWalter

private theorem perm_six_order_ne_eight (s : Perm (Fin 6)) : orderOf s ≠ 8 := by
  intro h
  have hd : orderOf s ∣ 4 := by
    rw [← s.lcm_cycleType, Multiset.lcm_dvd]
    intro n hn
    have hnd : n ∣ 8 := h ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have hns : n ≤ s.cycleType.sum := Multiset.le_sum_of_mem hn
    have hsum : s.cycleType.sum ≤ 6 := s.sum_cycleType_le
    have hn6 : n ≤ 6 := hns.trans hsum
    interval_cases n <;> norm_num at hnd <;> norm_num
  norm_num [h] at hd

private theorem natural_order_ne_eight (a : AutA6) (ha : a ∈ natural) :
    orderOf a ≠ 8 := by
  obtain ⟨s, rfl⟩ := ha
  change orderOf (permutationAction s) ≠ 8
  rw [orderOf_injective permutationAction permutationAction_injective]
  exact perm_six_order_ne_eight s

/-- The actual splitter acts outside the natural symmetric group. -/
theorem splitterAction_not_natural (e0 : CentralQuotient ≃* A6)
    (hperfect : Group.IsPerfect C) : normalizerAlternatingAction e0 splitterM ∉ natural := by
  intro h
  have hle : (vertexAlternatingAction e0).range ≤ natural := by
    rw [vertexAlternatingAction_range]
    exact sup_le inner_le_natural (zpowers_le.mpr h)
  apply natural_order_ne_eight (vertexAlternatingAction e0 eightQuotient)
    (hle ⟨eightQuotient, rfl⟩)
  rw [orderOf_injective (vertexAlternatingAction e0)
    (vertexAlternatingAction_injective e0 hperfect), orderOf_eightQuotient]

/-- The exceptional action identifies the literal vertex quotient with PGL₂(9). -/
theorem vertexQuotient_equiv_pgl2 (e0 : CentralQuotient ≃* A6)
    (hperfect : Group.IsPerfect C) : Nonempty (VertexQuotient ≃* PGL2 Nine.F) := by
  have hsq : normalizerAlternatingAction e0 splitterM ^ 2 = 1 := by
    rw [← map_pow, show splitterM ^ 2 = 1 from Subtype.ext splitter_square, map_one]
  let ea := (MonoidHom.ofInjective (vertexAlternatingAction_injective e0 hperfect)).trans
    (MulEquiv.subgroupCongr (vertexAlternatingAction_range e0))
  obtain ⟨ec⟩ := exceptional_extension_equiv_canonical
    (normalizerAlternatingAction e0 splitterM) hsq (splitterAction_not_natural e0 hperfect)
  obtain ⟨ep⟩ := canonicalExtension_equiv_pgl2
  exact ⟨(ea.trans ec).trans ep⟩

private theorem nine_odd_prime_power : IsOddPrimePower (Nat.card Nine.F) := by
  rw [Nine.card]
  exact ⟨3, 2, by decide, by decide, by decide, by decide⟩

private theorem nine_card_gt_three : 3 < Nat.card Nine.F := by
  rw [Nine.card]
  decide

/-- Any vertex comparison carries the perfect central quotient onto the
canonical projective special linear subgroup. -/
theorem projectiveComparison_range (e0 : CentralQuotient ≃* A6)
    (hperfect : Group.IsPerfect C) (eM : VertexQuotient ≃* PGL2 Nine.F) :
    (eM.toMonoidHom.comp quotientInclusion).range =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Nine.F)).range := by
  let := hperfect
  let : Finite (PGL2 Nine.F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let f := eM.toMonoidHom.comp quotientInclusion
  have hf : Function.Injective f := eM.injective.comp quotientInclusion_injective
  have hle : f.range ≤ commutator (PGL2 Nine.F) := by
    have hp : Group.IsPerfect f.range := Group.IsPerfect.range f
    rw [← Subgroup.commutator_eq_self (H := f.range)]
    exact Subgroup.commutator_mono le_top le_top
  rw [pgl2_commutator_eq_psl2_range_of_card_gt_three Nine.F
    nine_odd_prime_power nine_card_gt_three] at hle
  apply Subgroup.eq_of_le_of_card_ge hle
  have h1 : Nat.card f.range = Nat.card A6 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv).trans
      (Nat.card_congr e0.toEquiv)
  have h2 : Nat.card (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := Nine.F)).range = Nat.card A6 :=
    Nat.card_congr ((psl2EquivToPGLRange Nine.F).symm.trans psl2NineCoordinatesEquivAlt6).toEquiv
  exact Nat.le_of_eq (h2.trans h1.symm)

/-- Change the A₆ coordinates so that the projective comparison respects the
published inclusion. The adjustment is forced by the actual PSL₂ range. -/
noncomputable def compatibleCentralEquiv (e0 : CentralQuotient ≃* A6)
    (hperfect : Group.IsPerfect C) (eM : VertexQuotient ≃* PGL2 Nine.F) :
    CentralQuotient ≃* A6 :=
  (((MonoidHom.ofInjective (eM.injective.comp quotientInclusion_injective)).trans
    (MulEquiv.subgroupCongr (projectiveComparison_range e0 hperfect eM))).trans
    (psl2EquivToPGLRange Nine.F).symm).trans psl2NineCoordinatesEquivAlt6

theorem compatibleCentralEquiv_commutes (e0 : CentralQuotient ≃* A6)
    (hperfect : Group.IsPerfect C) (eM : VertexQuotient ≃* PGL2 Nine.F)
    (q : CentralQuotient) :
    eM (quotientInclusion q) = Matrix.ProjectiveSpecialLinearGroup.toPGL
      (psl2NineCoordinatesEquivAlt6.symm (compatibleCentralEquiv e0 hperfect eM q)) := by
  let r := ((MonoidHom.ofInjective (eM.injective.comp quotientInclusion_injective)).trans
    (MulEquiv.subgroupCongr (projectiveComparison_range e0 hperfect eM))) q
  change (r : PGL2 Nine.F) = Matrix.ProjectiveSpecialLinearGroup.toPGL
    (psl2NineCoordinatesEquivAlt6.symm
      (psl2NineCoordinatesEquivAlt6 ((psl2EquivToPGLRange Nine.F).symm r)))
  rw [psl2NineCoordinatesEquivAlt6.symm_apply_apply,
    ← psl2EquivToPGLRange_val]
  rw [MulEquiv.apply_symm_apply]

/-- The compatible comparison commutes with both original quotient maps. -/
theorem compatibleCentralEquiv_quotient_maps (e0 : CentralQuotient ≃* A6)
    (hperfect : Group.IsPerfect C) (eM : VertexQuotient ≃* PGL2 Nine.F) (c : C) :
    eM (vertexQuotientMap (centralInclusion c)) = Matrix.ProjectiveSpecialLinearGroup.toPGL
      (psl2NineCoordinatesEquivAlt6.symm
        (compatibleCentralEquiv e0 hperfect eM (centralQuotientMap c))) := by
  rw [← quotientInclusion_mk]
  exact compatibleCentralEquiv_commutes e0 hperfect eM (centralQuotientMap c)

/-- The quotient-map diagram also retains the literal inverting splitter. -/
theorem quotientInclusion_splitterAction (c : C) :
    quotientInclusion (centralQuotientMap (splitterAction c)) =
      vertexQuotientMap splitterM * quotientInclusion (centralQuotientMap c) *
        (vertexQuotientMap splitterM)⁻¹ := by
  rw [quotientInclusion_mk, quotientInclusion_mk, ← map_inv, ← map_mul, ← map_mul]
  apply congrArg vertexQuotientMap
  apply Subtype.ext
  rfl

/-- Compatible central and vertex coordinates for the exact published marking.
The only inputs are the independently produced A₆ central quotient and
perfectness of its central cover. -/
theorem exists_compatible_projective_comparison (e0 : CentralQuotient ≃* A6)
    (hperfect : Group.IsPerfect C) :
    ∃ (eC : CentralQuotient ≃* alternatingGroup (Fin 6))
      (eM : VertexQuotient ≃* PGL2 Nine.F),
      (∀ q, eM (quotientInclusion q) = Matrix.ProjectiveSpecialLinearGroup.toPGL
        (psl2NineCoordinatesEquivAlt6.symm (eC q))) ∧
      (∀ c : C, eM (vertexQuotientMap splitterM) *
          Matrix.ProjectiveSpecialLinearGroup.toPGL
            (psl2NineCoordinatesEquivAlt6.symm (eC (centralQuotientMap c))) *
          (eM (vertexQuotientMap splitterM))⁻¹ =
        Matrix.ProjectiveSpecialLinearGroup.toPGL
          (psl2NineCoordinatesEquivAlt6.symm (eC (centralQuotientMap (splitterAction c))))) := by
  obtain ⟨eM⟩ := vertexQuotient_equiv_pgl2 e0 hperfect
  let eC := compatibleCentralEquiv e0 hperfect eM
  have hc := compatibleCentralEquiv_commutes e0 hperfect eM
  refine ⟨eC, eM, hc, ?_⟩
  intro c
  rw [← hc, ← hc, ← map_inv, ← map_mul, ← map_mul, ← quotientInclusion_splitterAction]

end Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension
