module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Actors
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Models
public import Theory.GroupTheory.Fitting.Subgroup
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Component identities for the terminal row comparison

The offender actor is normal and contains the ambient quasisimple F*.
Its intrinsic generalized Fitting subgroup is exactly that component,
restricted along the actual inclusion. The same applies to the Thompson
image. This compares the components without identifying the actors.

For a field or graph extension, the source's involution supplements F*,
so the quotient is a two-group. Full-component rows have trivial quotient.
The triple-A₆ row is completed using its actual central covering witness.
These reductions do not assert the remaining F.6.18/B.5.6 intersection.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.6.18, printed pp.309–310, and the proof of 15.3.1, printed p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

namespace ComponentRows

private theorem fitting_normal_map {D : Type*} [Group D] [Finite D]
    (I : Subgroup D) [I.Normal] :
    (generalizedFitting I).map I.subtype ≤ generalizedFitting D := by
  rw [generalizedFitting, Subgroup.map_sup]
  apply sup_le
  · exact (show fittingSubgroupOf I ≤ fittingSubgroup D from
      le_sSup ⟨fittingSubgroupOf_normal I inferInstance,
        fittingSubgroupOf_isNilpotent I⟩).trans (fitting_le_generalizedFitting D)
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro C hC
    apply Subgroup.map_le_iff_le_comap.mp
    let _ := hC.2
    exact component_le_generalizedFitting D (C.map I.subtype)
      ⟨hC.1.trans' (inferInstance : I.Normal).isSubnormal,
        IsQuasisimple.of_mulEquiv (equivMapOfInjective C I.subtype I.subtype_injective)⟩

private theorem fitting_normal_overgroup {D : Type*} [Group D] [Finite D]
    (I : Subgroup D) [I.Normal]
    (hL : IsQuasisimple (generalizedFitting D)) (hle : generalizedFitting D ≤ I) :
    generalizedFitting I = (generalizedFitting D).subgroupOf I := by
  apply le_antisymm
  · intro x hx
    exact fitting_normal_map I (mem_map_of_mem I.subtype hx)
  · exact component_le_generalizedFitting I _
      ((show IsComponent D (generalizedFitting D) from
        ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hL⟩).subgroupOf hle)

private theorem quasisimple_not_solvable {D : Type*} [Group D]
    (h : IsQuasisimple D) : ¬ Group.IsSolvable D := by
  let _ := h
  let _ := h.simple
  let _ : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact Group.IsPerfect.not_isSolvable D

private theorem involution_quotient {D : Type*} [Group D] [Finite D]
    (g : D) (hg : orderOf g = 2) (ht : generalizedFitting D ⊔ zpowers g = ⊤) :
    IsPGroup 2 (D ⧸ generalizedFitting D) := by
  have hp : IsPGroup 2 (zpowers g) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2)
      (hg ▸ pow_orderOf_eq_one g)).isPGroup 2 _
  exact isPGroup_quotient_of_sup_eq_top _ _ hp ht

/-- The trivial quotient in a full-component F.6.18 row. -/
theorem quotient_of_fitting_top {D : Type*} [Group D] [Finite D]
    (ht : generalizedFitting D = ⊤) : IsPGroup 2 (D ⧸ generalizedFitting D) := by
  let _ : Subsingleton (D ⧸ (⊤ : Subgroup D)) := QuotientGroup.subsingleton_quotient_top
  let _ : Subsingleton (D ⧸ generalizedFitting D) :=
    (QuotientGroup.quotientMulEquivOfEq ht).injective.subsingleton
  exact IsPGroup.of_subsingleton 2 _

/-- The field involution already proves the quotient assertion of row (8). -/
theorem fieldRow_quotient {D : Type*} [Group D] [Finite D]
    (r : FSource.FieldExtensionRow (D := D)) : IsPGroup 2 (D ⧸ generalizedFitting D) :=
  involution_quotient r.element r.involution r.generated

/-- The graph involution already proves the quotient assertion of row (11). -/
theorem graphRow_quotient {D : Type*} [Group D] [Finite D]
    (r : FSource.GraphExtensionRow (D := D)) : IsPGroup 2 (D ⧸ generalizedFitting D) :=
  involution_quotient r.element r.involution r.generated

/-- Transport the source covering witness, including its actual central quotient. -/
theorem tripleAlternating_of_equiv {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) {n : ℕ} (h : FSource.TripleAlternating E n) :
    FSource.TripleAlternating D n := by
  let _ := h.perfect
  have hc : (center D).map e.toMonoidHom = center E := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr e ⟨x, hx⟩).property
    · intro x hx
      exact ⟨e.symm x, ((Subgroup.centerCongr e).symm ⟨x, hx⟩).property,
        e.apply_symm_apply x⟩
  exact ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
    h.center.map ((Subgroup.centerCongr e).trans ·),
    h.quotient.map ((QuotientGroup.congr _ _ e hc).trans ·)⟩

end ComponentRows

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H} (d : SourceInput V)
include d

/-- The Thompson image contains the ambient component, so its F* is that
same component with its original embedding. -/
theorem thompson_image_fitting_eq
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H))) :
    generalizedFitting ((thompsonGroup H).map coreProjection) =
      (generalizedFitting (coreQuotient H)).subgroupOf ((thompsonGroup H).map coreProjection) :=
  ComponentRows.fitting_normal_overgroup _ hL (d.fitting_le_thompson hL)

/-- A quasisimple ambient component rules out every solvable Thompson image. -/
theorem thompson_image_not_solvable
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H))) :
    ¬ Group.IsSolvable ((thompsonGroup H).map coreProjection) := by
  intro hs
  let _ := hs
  exact ComponentRows.quasisimple_not_solvable hL
    (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (d.fitting_le_thompson hL)))

/-- In particular the separate S₃ branch cannot occur above a quasisimple F*. -/
theorem thompson_image_not_symmetricThree
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (e : (thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) : False := by
  let _ : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let _ : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  exact d.thompson_image_not_solvable hL
    (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

/-- F.6.18(6)'s full triple-A₆ component supplies all three required outputs. -/
theorem component_row_tripleSix
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (ht : generalizedFitting (coreQuotient H) = ⊤)
    (h : FSource.TripleAlternating (coreQuotient H) 6) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  let e : (thompsonGroup H).map coreProjection ≃* coreQuotient H :=
    (MulEquiv.subgroupCongr (d.thompson_image_eq_top_of_fitting_top hL ht)).trans topEquiv
  exact ⟨.tripleSix (ComponentRows.tripleAlternating_of_equiv e h),
    .tripleAlternatingSix h, ComponentRows.quotient_of_fitting_top ht⟩

variable [IsElementaryAbelian 2 (moduleClosure V)]

/-- F* of the actual offender actor is the restricted ambient component. -/
theorem offender_fitting_eq
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H))) :
    generalizedFitting d.offenderGroup =
      (generalizedFitting (coreQuotient H)).subgroupOf d.offenderGroup := by
  let _ : d.offenderGroup.Normal := Representation.BinaryOffender.offenderSubgroup_normal _
  exact ComponentRows.fitting_normal_overgroup d.offenderGroup hL
    ((d.fitting_le_thompson hL).trans d.thompson_image_le_offender)

/-- Quasisimplicity passes to the offender's F*, without equating either actor
with the ambient quotient and without a three-rank hypothesis. -/
theorem offender_fitting_quasisimple
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H))) :
    IsQuasisimple (generalizedFitting d.offenderGroup) := by
  let _ := hL
  have he : generalizedFitting (coreQuotient H) ≃* generalizedFitting d.offenderGroup :=
    (subgroupOfEquivOfLe
      ((d.fitting_le_thompson hL).trans d.thompson_image_le_offender)).symm.trans
      (MulEquiv.subgroupCongr (d.offender_fitting_eq hL).symm)
  exact IsQuasisimple.of_mulEquiv he

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
