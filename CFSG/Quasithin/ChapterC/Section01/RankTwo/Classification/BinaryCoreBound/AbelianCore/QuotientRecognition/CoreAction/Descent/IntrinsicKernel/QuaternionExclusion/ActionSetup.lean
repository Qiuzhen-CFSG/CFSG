module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.IntrinsicKernel.MaximumOffender
public import Theory.GroupTheory.PCoreSurjective
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction

/-!
# The literal central-product action in the SL₂(7) branch

Write H for the faithful conjugation image on D=[O₂(J),L] and Q for the
image of O₂(J). Since the action kernel lies in O₂(J), Q=O₂(H) and its
preimage is the original O₂(J). The supplied component equivalence defines
an injective SL₂(7)→H retaining every conjugating representative. When D is
abelian, this image commutes with Q and generates H together with Q.
Their intersection is precisely the center of SL₂(7); consequently Q is
also the full centralizer of that matrix component.

A determinant-one matrix of size two squaring to one is scalar in odd
characteristic. Its equality with its adjugate gives equal diagonal entries
and zero off-diagonal entries. Thus every elementary subgroup meets the
matrix component only in Q. In the original group, this gives E∩L≤O₂(J).
It does not give E≤O₂(J), because E may have an image across both factors.
The remaining best-offender exclusion must treat those images.

The elementary-core specialization retains the faithful binary action and
full generation by component displacements. No natural-module quotient,
module catalogue, or component offender is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137; B.2.3–5, printed pp.75–76. The elementary matrix argument
also appears in Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction.
-/

public section
open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterC.BinaryMS

local instance quaternionExclusionPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem sl2_square_one_central {F : Type*} [CommRing F] [IsDomain F]
    (hF : (2 : F) ≠ 0)
    (a : Matrix.SpecialLinearGroup (Fin 2) F) (ha : a ^ 2 = 1) :
    a ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hi : a = a⁻¹ := eq_inv_of_mul_eq_one_left (by simpa only [pow_two] using ha)
  have hadj : (a : Matrix (Fin 2) (Fin 2) F) =
      (a : Matrix (Fin 2) (Fin 2) F).adjugate := congrArg Subtype.val hi
  have h00 := congrFun (congrFun hadj 0) 0
  have h01 := congrFun (congrFun hadj 0) 1
  have h10 := congrFun (congrFun hadj 1) 0
  rw [Matrix.adjugate_fin_two] at h00 h01 h10
  change a 0 0 = a 1 1 at h00
  change a 0 1 = -a 0 1 at h01
  change a 1 0 = -a 1 0 at h10
  have hz01 : a 0 1 = 0 := by
    apply (mul_eq_zero.mp (show (2 : F) * a 0 1 = 0 by linear_combination h01)).resolve_left hF
  have hz10 : a 1 0 = 0 := by
    apply (mul_eq_zero.mp (show (2 : F) * a 1 0 = 0 by linear_combination h10)).resolve_left hF
  have hscalar : (a : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (a 0 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, hz01, hz10, ← h00]
  rw [mem_center_iff]
  intro b
  apply Subtype.ext
  change (b : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) =
    (a : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F)
  rw [hscalar]
  exact (Matrix.scalar_comm _ (fun _ => Commute.all _ _) _).symm

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)

/-- The image of the original ambient two-core on the commutator core. -/
abbrev Input.coreActionTwoCore : Subgroup h.coreAmbientConjugation.range :=
  (pCore 2 J).map h.coreAmbientConjugation.rangeRestrict

/-- The action kernel is contained in the original two-core, so taking its
image loses no information about containment in the two-core. -/
theorem Input.coreActionTwoCore_comap :
    h.coreActionTwoCore.comap h.coreAmbientConjugation.rangeRestrict = pCore 2 J := by
  apply Subgroup.comap_map_eq_self
  rw [h.coreAmbientConjugation_rangeKernel]
  exact h.core_centralizer_le

/-- The commuting factor is a genuine normal two-group in the action image. -/
theorem Input.coreActionTwoCore_normal : h.coreActionTwoCore.Normal :=
  (inferInstance : (pCore 2 J).Normal).map _
    h.coreAmbientConjugation.rangeRestrict_surjective

theorem Input.coreActionTwoCore_isPGroup : IsPGroup 2 h.coreActionTwoCore :=
  pCore_isPGroup.map _

/-- The image of O₂(J) is also the intrinsic two-core of the faithful
ambient action group. This does not identify the original action kernel
with O₂(J). -/
theorem Input.coreActionTwoCore_eq_pCore :
    h.coreActionTwoCore = pCore 2 h.coreAmbientConjugation.range := by
  have hk : IsPGroup 2 h.coreAmbientConjugation.rangeRestrict.ker := by
    apply pCore_isPGroup.of_injective
      (Subgroup.inclusion (show h.coreAmbientConjugation.rangeRestrict.ker ≤ pCore 2 J from ?_))
      (Subgroup.inclusion_injective _)
    rw [h.coreAmbientConjugation_rangeKernel]
    exact h.core_centralizer_le
  change (pCore 2 J).map h.coreAmbientConjugation.rangeRestrict = _
  rw [← h.coreAmbientConjugation.rangeRestrict.comap_pCore_of_ker_isPGroup
    h.coreAmbientConjugation.rangeRestrict_surjective hk, Subgroup.map_comap_eq_self]
  rw [h.coreAmbientConjugation.rangeRestrict.range_eq_top_of_surjective
    h.coreAmbientConjugation.rangeRestrict_surjective]
  exact le_top

/-- Containment of an action image in the commuting factor is exactly the
original containment in O₂(J). -/
theorem Input.map_coreAction_le_twoCore_iff (E : Subgroup J) :
    E.map h.coreAmbientConjugation.rangeRestrict ≤ h.coreActionTwoCore ↔
      E ≤ pCore 2 J := by
  rw [Subgroup.map_le_iff_le_comap, h.coreActionTwoCore_comap]

/-- The component meets the commuting factor in precisely its central-cover
kernel, using the original intrinsic and ambient two-cores. -/
theorem Input.coreComponentEmbedding_comap_twoCore
    (hc : IsMulCommutative (commutatorCore L)) :
    h.coreActionTwoCore.comap h.coreComponentEmbedding =
      center h.coreConjugation.range := by
  rw [← h.abelianCore_componentProjection_kernel_eq_center hc]
  ext a
  obtain ⟨l, rfl⟩ := h.coreConjugation.rangeRestrict_surjective a
  change h.coreComponentEmbedding (h.coreConjugation.rangeRestrict l) ∈
    h.coreActionTwoCore ↔ h.coreComponentProjection (h.coreConjugation.rangeRestrict l) = 1
  rw [h.coreComponentEmbedding_apply, h.coreComponentProjection_apply,
    h.quotientEquiv.map_eq_one_iff]
  change h.coreAmbientConjugation.rangeRestrict (l : J) ∈ h.coreActionTwoCore ↔
    (l : L ⧸ pCore 2 L) = 1
  rw [QuotientGroup.eq_one_iff]
  change (l : J) ∈ h.coreActionTwoCore.comap h.coreAmbientConjugation.rangeRestrict ↔ _
  rw [h.coreActionTwoCore_comap]
  constructor
  · intro hl
    obtain ⟨m, hm, he⟩ := h.componentCore_eq_inf.ge ⟨hl, l.property⟩
    exact (Subtype.ext he : m = l) ▸ hm
  · intro hl
    exact (h.componentCore_eq_inf.le (mem_map_of_mem L.subtype hl)).1

/-- The supplied cover equivalence gives an actual embedded SL₂(7) in the
ambient conjugation image. -/
noncomputable def Input.coreSL2SevenEmbedding
    (e : h.coreConjugation.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) →* h.coreAmbientConjugation.range :=
  h.coreComponentEmbedding.comp e.symm.toMonoidHom

variable (e : h.coreConjugation.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 7))

theorem Input.coreSL2SevenEmbedding_injective :
    Function.Injective (h.coreSL2SevenEmbedding e) :=
  h.coreComponentEmbedding_injective.comp e.symm.injective

/-- The marking preserves the literal action of each component representative. -/
theorem Input.coreSL2SevenEmbedding_component (l : L) :
    h.coreSL2SevenEmbedding e (e (h.coreConjugation.rangeRestrict l)) =
      h.coreAmbientConjugation.rangeRestrict l := by
  change h.coreComponentEmbedding (e.symm (e (h.coreConjugation.rangeRestrict l))) = _
  rw [e.symm_apply_apply, h.coreComponentEmbedding_apply]

theorem Input.coreSL2SevenEmbedding_range :
    (h.coreSL2SevenEmbedding e).range = h.coreComponentEmbedding.range := by
  rw [Input.coreSL2SevenEmbedding, MonoidHom.range_comp,
    e.symm.toMonoidHom.range_eq_top_of_surjective e.symm.surjective,
    ← MonoidHom.range_eq_map]

theorem Input.coreSL2SevenEmbedding_normal : (h.coreSL2SevenEmbedding e).range.Normal := by
  rw [h.coreSL2SevenEmbedding_range e]
  exact h.coreComponentEmbedding_normal

/-- These are the two generating factors of the faithful ambient action. -/
theorem Input.coreSL2SevenEmbedding_sup_twoCore :
    h.coreActionTwoCore ⊔ (h.coreSL2SevenEmbedding e).range = ⊤ := by
  rw [h.coreSL2SevenEmbedding_range e]
  exact h.coreComponentImage_sup_twoCore

/-- The two factors commute; the assertion concerns their literal action images. -/
theorem Input.coreSL2SevenEmbedding_commutes_twoCore
    (hc : IsMulCommutative (commutatorCore L)) :
    ⁅h.coreActionTwoCore, (h.coreSL2SevenEmbedding e).range⁆ = ⊥ := by
  rw [h.coreSL2SevenEmbedding_range e]
  exact h.abelianCore_componentImage_commutes_twoCore hc

/-- The overlap of the two factors is precisely the center of the matrix cover. -/
theorem Input.coreSL2SevenEmbedding_comap_twoCore
    (hc : IsMulCommutative (commutatorCore L)) :
    h.coreActionTwoCore.comap (h.coreSL2SevenEmbedding e) =
      center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) := by
  change (h.coreActionTwoCore.comap h.coreComponentEmbedding).comap e.symm.toMonoidHom = _
  rw [h.coreComponentEmbedding_comap_twoCore hc]
  ext a
  constructor
  · intro ha
    have hh := (centerCongr e ⟨e.symm a, ha⟩).property
    change e (e.symm a) ∈ center _ at hh
    simpa only [e.apply_symm_apply] using hh
  · intro ha
    exact (centerCongr e.symm ⟨a, ha⟩).property

/-- The commuting two-core is exactly the centralizer of the marked cover
in the ambient action group. -/
theorem Input.coreSL2SevenEmbedding_centralizer
    (hc : IsMulCommutative (commutatorCore L)) :
    centralizer ((h.coreSL2SevenEmbedding e).range : Set h.coreAmbientConjugation.range) =
      h.coreActionTwoCore := by
  let f := h.coreSL2SevenEmbedding e
  have hcomm : h.coreActionTwoCore ≤ centralizer (f.range : Set _) :=
    commutator_eq_bot_iff_le_centralizer.mp (h.coreSL2SevenEmbedding_commutes_twoCore e hc)
  apply le_antisymm _ hcomm
  intro x hx
  let := h.coreActionTwoCore_normal
  have hxjoin : x ∈ h.coreActionTwoCore ⊔ f.range := by
    rw [h.coreSL2SevenEmbedding_sup_twoCore e]
    trivial
  obtain ⟨n, hn, k, hk, rfl⟩ := mem_sup_of_normal_left.mp hxjoin
  obtain ⟨a, rfl⟩ := hk
  have ha : a ∈ center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) := by
    rw [mem_center_iff]
    intro b
    apply h.coreSL2SevenEmbedding_injective e
    have hb := hx (f b) ⟨b, rfl⟩
    have hncomm := hcomm hn (f b) ⟨b, rfl⟩
    change f b * (n * f a) = (n * f a) * f b at hb
    rw [← mul_assoc, hncomm, mul_assoc, mul_assoc] at hb
    simpa only [map_mul] using (mul_left_cancel hb)
  have haQ : f a ∈ h.coreActionTwoCore :=
    (h.coreSL2SevenEmbedding_comap_twoCore e hc).ge ha
  exact h.coreActionTwoCore.mul_mem hn haQ

/-- Elementary subgroups meet the marked cover only inside the commuting
two-core: every square-one matrix in SL₂(7) is central. -/
theorem Input.coreSL2SevenEmbedding_elementary_inter_le_twoCore
    (hc : IsMulCommutative (commutatorCore L))
    (A : Subgroup h.coreAmbientConjugation.range) (hA : IsElementaryAbelian 2 A) :
    A ⊓ (h.coreSL2SevenEmbedding e).range ≤ h.coreActionTwoCore := by
  rintro a ⟨ha, b, rfl⟩
  let := hA
  have hs : b ^ 2 = 1 := by
    apply h.coreSL2SevenEmbedding_injective e
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ ha
  exact (h.coreSL2SevenEmbedding_comap_twoCore e hc).ge
    (sl2_square_one_central (by decide : (2 : ZMod 7) ≠ 0) b hs)

include h e in
/-- In the original MS group, an elementary subgroup meets L only in
O₂(J). This leaves open elementary subgroups with a nontrivial diagonal
image across the two commuting factors. -/
theorem Input.elementary_inter_component_le_core_of_SL2Seven
    (hc : IsMulCommutative (commutatorCore L))
    (E : Subgroup J) (hE : IsElementaryAbelian 2 E) :
    E ⊓ L ≤ pCore 2 J := by
  intro x hx
  have hl : h.coreAmbientConjugation.rangeRestrict x ∈
      (h.coreSL2SevenEmbedding e).range := by
    rw [h.coreSL2SevenEmbedding_range e, h.coreComponentEmbedding_range]
    exact mem_map_of_mem _ hx.2
  have hxQ := h.coreSL2SevenEmbedding_elementary_inter_le_twoCore e hc
    (E.map h.coreAmbientConjugation.rangeRestrict) (hE.map _)
    ⟨mem_map_of_mem _ hx.1, hl⟩
  exact h.coreActionTwoCore_comap.le hxQ

variable [IsElementaryAbelian 2 (commutatorCore L)]

/-- The marked matrix component generates the entire module by displacements. -/
theorem Input.coreSL2SevenEmbedding_full_commutator :
    subspaceCommutator h.coreAmbientRepresentation ⊤
      (h.coreSL2SevenEmbedding e).range = ⊤ := by
  rw [h.coreSL2SevenEmbedding_range e, h.coreComponentEmbedding_range]
  exact h.coreAmbientRepresentation_full_commutator

end CFSG.Quasithin.ChapterC.BinaryMS
