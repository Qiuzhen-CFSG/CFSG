module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.CentralCover.Action
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Theory.GroupTheory.Covering

/-!
# The marked perfect central cover of A₆ inside J₂

The ten points fixed by the published element x give an action of its literal
centralizer C. Checked words in C act as the standard generators of PSL₂(9).
The central quotient has order 360, so its action is faithful with precisely
that image. The existing exceptional isomorphism then supplies an actual
surjection C → A₆ with kernel XC and compatible central quotient map.

A checked commutator equal to x absorbs XC in the derived subgroup. Since A₆
is perfect and centerless, C is perfect and has center exactly XC. This proves
the central-cover part of Aschbacher, *Sporadic Groups* (1994), 47.3(1),
pp.261–262, for the published marking, under only the permitted |M| = 2160.
No assertion about ambient simplicity or the full normalizer quotient is used.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension
open Subgroup Atlas.Comparisons.Exceptional
open scoped MatrixGroups

/-- The isomorphism induced by the literal ten-point action. -/
noncomputable def centralQuotientEquivPSL2Nine (hM : Nat.card M = 2160) :
    CentralQuotient ≃* PSL(2, Nine.F) :=
  (MonoidHom.ofInjective (CentralCover.quotientAction_injective hM)).trans
    ((MulEquiv.subgroupCongr (CentralCover.range_eq_nine hM)).trans
      (MonoidHom.ofInjective Nine.permutation_injective).symm)

theorem centralQuotientEquivPSL2Nine_action (hM : Nat.card M = 2160) (q : CentralQuotient) :
    Nine.permutation (centralQuotientEquivPSL2Nine hM q) = CentralCover.quotientAction q := by
  exact MonoidHom.apply_ofInjective_symm Nine.permutation_injective _

/-- The central quotient is the actual alternating group on six letters. -/
noncomputable def centralQuotientEquivAlt6 (hM : Nat.card M = 2160) :
    CentralQuotient ≃* alternatingGroup (Fin 6) :=
  (centralQuotientEquivPSL2Nine hM).trans psl2NineCoordinatesEquivAlt6

theorem centralQuotientEquivAlt6_action (hM : Nat.card M = 2160) (q : CentralQuotient) :
    TriplePartitions.action (centralQuotientEquivAlt6 hM q) = CentralCover.quotientAction q := by
  exact (psl2NineCoordinatesEquivAlt6_action _).trans
    (centralQuotientEquivPSL2Nine_action hM q)

/-- The surjection is defined on the full concrete centralizer C. -/
noncomputable def centralCoverHom (hM : Nat.card M = 2160) : C →* alternatingGroup (Fin 6) :=
  (centralQuotientEquivAlt6 hM).toMonoidHom.comp centralQuotientMap

/-- Compatibility retains precisely the quotient by X.subgroupOf C. -/
theorem centralCoverHom_quotient (hM : Nat.card M = 2160) (c : C) :
    centralQuotientEquivAlt6 hM (centralQuotientMap c) = centralCoverHom hM c := rfl

theorem centralCoverHom_surjective (hM : Nat.card M = 2160) :
    Function.Surjective (centralCoverHom hM) :=
  (centralQuotientEquivAlt6 hM).surjective.comp (QuotientGroup.mk'_surjective XC)

theorem centralCoverHom_ker (hM : Nat.card M = 2160) : (centralCoverHom hM).ker = XC := by
  ext c
  change centralQuotientEquivAlt6 hM (centralQuotientMap c) = 1 ↔ c ∈ XC
  rw [← (centralQuotientEquivAlt6 hM).map_one, (centralQuotientEquivAlt6 hM).injective.eq_iff]
  exact QuotientGroup.eq_one_iff _

/-- The actual centralizer is perfect, using the checked central commutator. -/
theorem C_isPerfect (hM : Nat.card M = 2160) : Group.IsPerfect C := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  constructor
  have h := CentralExtension.ker_sup_commutator_eq_top_of_surjective
    (centralCoverHom hM) (centralCoverHom_surjective hM)
  rw [centralCoverHom_ker hM, sup_eq_right.mpr CentralCover.XC_le_commutator] at h
  exact h

/-- There is no additional center beyond the literal marked subgroup. -/
theorem center_C_eq_XC (hM : Nat.card M = 2160) : center C = XC := by
  apply le_antisymm ?_ XC_le_center
  intro c hc
  rw [← centralCoverHom_ker hM]
  change centralCoverHom hM c = 1
  have hm : centralCoverHom hM c ∈ center (alternatingGroup (Fin 6)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨d, rfl⟩ := centralCoverHom_surjective hM y
    simpa only [map_mul] using congrArg (centralCoverHom hM) (mem_center_iff.mp hc d)
  rw [alternatingGroup.center_eq_bot (by simp)] at hm
  exact hm

/-- The center has the required marking after inclusion in the ambient carrier. -/
theorem map_center_C (hM : Nat.card M = 2160) : (center C).map C.subtype = X := by
  rw [center_C_eq_XC hM]
  exact Subgroup.map_subgroupOf_eq_of_le X_le_C

/-- Quasisimplicity is proved for C itself and its genuine center quotient. -/
theorem C_isQuasisimple (hM : Nat.card M = 2160) : Theory.GroupTheory.IsQuasisimple C := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  refine { toIsPerfect := C_isPerfect hM, simple := ?_ }
  let e : (C ⧸ center C) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq (center_C_eq_XC hM)).trans (centralQuotientEquivAlt6 hM)
  exact e.isSimpleGroup_congr.mpr inferInstance

end Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension
