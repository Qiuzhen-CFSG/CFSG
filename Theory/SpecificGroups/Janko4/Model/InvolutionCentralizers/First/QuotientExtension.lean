module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Action
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension.Matrix

/-!
# The actual normal series in the first J₄ involution centralizer

Pull back the scalar subgroup and the perfect triple cover through the proved
full quotient map C → C/O₂(C) ≃ actionGroup. The resulting actual normal subgroups
Q ≤ R ≤ H ≤ C have sections C₃, M₂₂, 3.M₂₂, C₂ and Aut(M₂₂), with all quotient
maps retained. Conjugation by a preimage of the marked odd matrix is outer on
H/R and inverts the marked scalar of R/Q.

This establishes the full quotient 3.M₂₂.2 in GLS3 Table 5.3i, for the first
centralizer of Aschbacher–Smith 16.1.5(9), printed p.1172. Extraspecial plus-type
recognition for Q is separate. The construction does not assume a splitting.
-/

@[expose] public section

namespace Janko4.InvolutionCentralizers.First.QuotientExtension

open Subgroup
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Sporadic.Mathieu

/-- The intrinsic two-core of the literal first centralizer. -/
abbrev Q : Subgroup centralizer := pCore 2 centralizer

/-- The preimage of the scalar subgroup under the actual quotient action. -/
noncomputable def R : Subgroup centralizer :=
  scalarSubgroup.comap centralizerExtension.rightHom

/-- The preimage of the genuine triple cover under the actual quotient action. -/
noncomputable def H : Subgroup centralizer :=
  coverSubgroup.comap centralizerExtension.rightHom

instance R_normal : R.Normal := inferInstanceAs
  (scalarSubgroup.comap centralizerExtension.rightHom).Normal

instance H_normal : H.Normal := inferInstanceAs
  (coverSubgroup.comap centralizerExtension.rightHom).Normal

theorem centralizerProjection_ker : centralizerExtension.rightHom.ker = Q := by
  have hi : centralizerExtension.inl = Q.subtype :=
    MonoidHom.ext centralizerExtension_inl
  rw [← centralizerExtension.range_inl_eq_ker_rightHom, hi, Subgroup.range_subtype]

theorem Q_le_R : Q ≤ R := by
  rw [← centralizerProjection_ker]
  exact MonoidHom.ker_le_comap _ _

theorem R_le_H : R ≤ H := Subgroup.comap_mono scalarSubgroup_le_cover

theorem Q_le_H : Q ≤ H := Q_le_R.trans R_le_H

/-- Relative normality for every quotient in the actual normal series. -/
theorem normalSeries : Q ≤ R ∧ R ≤ H ∧
    (Q.subgroupOf R).Normal ∧ (R.subgroupOf H).Normal ∧
    (Q.subgroupOf H).Normal ∧ H.Normal ∧ R.Normal :=
  ⟨Q_le_R, R_le_H, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance⟩

/-- The restriction of the actual quotient map to the preimage of the scalar. -/
noncomputable def scalarProjection : R →* scalarSubgroup :=
  centralizerExtension.rightHom.subgroupComap scalarSubgroup

theorem scalarProjection_surjective : Function.Surjective scalarProjection :=
  MonoidHom.subgroupComap_surjective_of_surjective _ _
    centralizerExtension.rightHom_surjective

theorem scalarProjection_ker : scalarProjection.ker = Q.subgroupOf R := by
  ext x
  rw [← centralizerProjection_ker]
  change scalarProjection x = 1 ↔ centralizerExtension.rightHom x.val = 1
  exact Subtype.ext_iff

/-- R/Q is the actual scalar subgroup of the matrix quotient. -/
noncomputable def RQuotientEquivScalar : (R ⧸ Q.subgroupOf R) ≃* scalarSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq scalarProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective scalarProjection scalarProjection_surjective)

theorem RQuotientEquivScalar_mk (r : R) :
    RQuotientEquivScalar (QuotientGroup.mk' (Q.subgroupOf R) r) =
      scalarProjection r := rfl

/-- The order-three section in the literal first centralizer. -/
noncomputable def RQuotientEquivC3 :
    (R ⧸ Q.subgroupOf R) ≃* Multiplicative (ZMod 3) :=
  RQuotientEquivScalar.trans scalarSubgroupEquivC3

/-- The actual quotient map from H to the concrete triple cover. -/
noncomputable def coverProjection : H →* M22TripleCover :=
  (Subgroup.subgroupOfEquivOfLe derivedGroup_le_actionGroup).toMonoidHom.comp
    (centralizerExtension.rightHom.subgroupComap coverSubgroup)

theorem coverProjection_surjective : Function.Surjective coverProjection :=
  (Subgroup.subgroupOfEquivOfLe derivedGroup_le_actionGroup).surjective.comp
    (MonoidHom.subgroupComap_surjective_of_surjective _ _
      centralizerExtension.rightHom_surjective)

theorem coverProjection_inclusion (h : H) :
    coverInclusion (coverProjection h) = centralizerExtension.rightHom h.val := rfl

theorem coverProjection_ker : coverProjection.ker = Q.subgroupOf H := by
  ext x
  rw [← centralizerProjection_ker]
  change coverProjection x = 1 ↔ centralizerExtension.rightHom x.val = 1
  constructor
  · intro hx
    have he := congrArg coverInclusion hx
    simpa only [coverProjection_inclusion, map_one] using he
  · intro hx
    apply (Subgroup.inclusion_injective derivedGroup_le_actionGroup)
    change coverInclusion (coverProjection x) = coverInclusion 1
    rw [coverProjection_inclusion, hx, map_one]

/-- H/Q is the given perfect triple cover, retaining its inclusion in C/Q. -/
noncomputable def HQuotientEquivCover : (H ⧸ Q.subgroupOf H) ≃* M22TripleCover :=
  (QuotientGroup.quotientMulEquivOfEq coverProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective coverProjection coverProjection_surjective)

theorem HQuotientEquivCover_mk (h : H) :
    HQuotientEquivCover (QuotientGroup.mk' (Q.subgroupOf H) h) = coverProjection h := rfl

/-- The native M₂₂ projection of the specified triple cover. -/
noncomputable def coverCentralProjection : M22TripleCover →* M22 :=
  M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center M22TripleCover))

theorem coverCentralProjection_ker :
    coverCentralProjection.ker = Subgroup.center M22TripleCover := by
  rw [coverCentralProjection, MonoidHom.ker_comp_of_injective _ _
    M22TripleCover.centralQuotientEquiv.injective, QuotientGroup.ker_mk']

/-- The map on H obtained by the actual covering quotient onto M₂₂. -/
noncomputable def mathieuProjection : H →* M22 :=
  coverCentralProjection.comp coverProjection

theorem mathieuProjection_surjective : Function.Surjective mathieuProjection :=
  (M22TripleCover.centralQuotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective _)).comp coverProjection_surjective

theorem mathieuProjection_ker : mathieuProjection.ker = R.subgroupOf H := by
  ext x
  change coverCentralProjection (coverProjection x) = 1 ↔
    centralizerExtension.rightHom x.val ∈ scalarSubgroup
  rw [← MonoidHom.mem_ker, coverCentralProjection_ker,
    ← coverProjection_inclusion, coverInclusion_mem_scalar]

/-- H/R is the native M₂₂, with the covering identification preserved. -/
noncomputable def HQuotientEquivM22 : (H ⧸ R.subgroupOf H) ≃* M22 :=
  (QuotientGroup.quotientMulEquivOfEq mathieuProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective mathieuProjection mathieuProjection_surjective)

theorem HQuotientEquivM22_mk (h : H) :
    HQuotientEquivM22 (QuotientGroup.mk' (R.subgroupOf H) h) =
      M22TripleCover.centralQuotientEquiv
        (QuotientGroup.mk' (Subgroup.center M22TripleCover) (coverProjection h)) := rfl

/-- The index-two character on the literal centralizer. -/
noncomputable def centralizerOuterCharacter : centralizer →* Multiplicative (ZMod 2) :=
  outerCharacter.comp centralizerExtension.rightHom

theorem centralizerOuterCharacter_ker : centralizerOuterCharacter.ker = H := by
  rw [centralizerOuterCharacter, ← MonoidHom.comap_ker, outerCharacter_ker]
  rfl

/-- C/H is the cyclic group of order two. -/
noncomputable def centralizerQuotientEquivC2 : (centralizer ⧸ H) ≃* Multiplicative (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq centralizerOuterCharacter_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective centralizerOuterCharacter
      (outerCharacter_surjective.comp centralizerExtension.rightHom_surjective))

theorem centralizerQuotientEquivC2_mk (c : centralizer) :
    centralizerQuotientEquivC2 (QuotientGroup.mk' H c) =
      outerCharacter (quotientEquiv (QuotientGroup.mk' Q c)) := by
  change outerCharacter (centralizerExtension.rightHom c) = _
  rw [centralizerExtension_rightHom]

/-- The action of the literal centralizer on the native M₂₂ section. -/
noncomputable def centralizerMathieuAction : centralizer →* MulAut M22 :=
  quotientConjugation.comp centralizerExtension.rightHom

theorem centralizerMathieuAction_ker : centralizerMathieuAction.ker = R := by
  rw [centralizerMathieuAction, ← MonoidHom.comap_ker, quotientConjugation_ker]
  rfl

/-- Conjugation by C on its actual normal subgroup H. -/
noncomputable def conjugateCover (c : centralizer) (h : H) : H :=
  ⟨c * h.val * c⁻¹, H_normal.conj_mem _ h.property c⟩

theorem coverProjection_conjugate (c : centralizer) (h : H) :
    coverProjection (conjugateCover c h) =
      derivedConjugation (centralizerExtension.rightHom c) (coverProjection h) := by
  apply Subtype.ext
  change ((centralizerExtension.rightHom (c * h.val * c⁻¹)) : Matrix12ˣ) = _
  rw [map_mul, map_mul, map_inv]
  rfl

/-- The automorphism identification is induced by conjugation on H/R. -/
theorem centralizerMathieuAction_apply (c : centralizer) (h : H) :
    centralizerMathieuAction c (mathieuProjection h) =
      mathieuProjection (conjugateCover c h) := by
  change MulAut.centralQuotientAction M22TripleCover.centralQuotientEquiv
    (derivedConjugation (centralizerExtension.rightHom c))
    (M22TripleCover.centralQuotientEquiv
      (QuotientGroup.mk' (Subgroup.center M22TripleCover) (coverProjection h))) = _
  rw [MulAut.centralQuotientAction_apply, ← coverProjection_conjugate]
  rfl

/-- C/R is the full native automorphism group through its actual conjugation action. -/
noncomputable def centralizerQuotientEquivAut : (centralizer ⧸ R) ≃* MulAut M22 :=
  (QuotientGroup.quotientMulEquivOfEq centralizerMathieuAction_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective centralizerMathieuAction
      (quotientConjugation_surjective.comp centralizerExtension.rightHom_surjective))

theorem centralizerQuotientEquivAut_mk (c : centralizer) :
    centralizerQuotientEquivAut (QuotientGroup.mk' R c) =
      quotientConjugation (quotientEquiv (QuotientGroup.mk' Q c)) := by
  change quotientConjugation (centralizerExtension.rightHom c) = _
  rw [centralizerExtension_rightHom]

/-- A preimage in the literal centralizer of the marked outer matrix. -/
noncomputable def markedOuter : centralizer :=
  (centralizerExtension.rightHom_surjective outerElement).choose

theorem markedOuter_projection :
    centralizerExtension.rightHom markedOuter = outerElement :=
  (centralizerExtension.rightHom_surjective outerElement).choose_spec

theorem markedOuter_not_mem_H : markedOuter ∉ H := by
  change centralizerExtension.rightHom markedOuter ∉ coverSubgroup
  rw [markedOuter_projection]
  exact outerElement_not_mem_cover

theorem markedOuter_action_outer :
    ¬ ∃ x : M22, centralizerMathieuAction markedOuter = MulAut.conj x := by
  simpa only [centralizerMathieuAction, MonoidHom.comp_apply, markedOuter_projection]
    using quotientConjugation_outer

/-- A preimage in R of the distinguished covering scalar. -/
noncomputable def markedScalar : R :=
  (scalarProjection_surjective scalarGenerator).choose

theorem markedScalar_projection : scalarProjection markedScalar = scalarGenerator :=
  (scalarProjection_surjective scalarGenerator).choose_spec

/-- Conjugation takes place inside the actual normal subgroup R. -/
noncomputable def markedConjugate : R :=
  ⟨markedOuter * markedScalar.val * markedOuter⁻¹,
    R_normal.conj_mem _ markedScalar.property markedOuter⟩

/-- The marked order-three section retains the inversion by the outer coset. -/
theorem markedOuter_inverts_scalar_section :
    QuotientGroup.mk' (Q.subgroupOf R) markedConjugate =
      (QuotientGroup.mk' (Q.subgroupOf R) markedScalar)⁻¹ := by
  apply RQuotientEquivScalar.injective
  rw [map_inv, RQuotientEquivScalar_mk, RQuotientEquivScalar_mk]
  apply Subtype.ext
  change centralizerExtension.rightHom
      (markedOuter * markedScalar.val * markedOuter⁻¹) =
    (centralizerExtension.rightHom markedScalar.val)⁻¹
  have hz := congrArg Subtype.val markedScalar_projection
  change centralizerExtension.rightHom markedScalar.val = scalarElement at hz
  rw [map_mul, map_mul, map_inv, markedOuter_projection, hz, outerElement_conj_scalar]

theorem markedScalar_section_order :
    orderOf (QuotientGroup.mk' (Q.subgroupOf R) markedScalar) = 3 := by
  rw [← orderOf_injective RQuotientEquivScalar.toMonoidHom
    RQuotientEquivScalar.injective]
  change orderOf (RQuotientEquivScalar (QuotientGroup.mk' (Q.subgroupOf R) markedScalar)) = 3
  rw [RQuotientEquivScalar_mk, markedScalar_projection]
  exact scalarGenerator_order

end Janko4.InvolutionCentralizers.First.QuotientExtension
