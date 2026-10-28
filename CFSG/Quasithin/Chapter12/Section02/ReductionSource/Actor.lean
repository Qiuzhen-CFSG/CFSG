module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Selection
public import Theory.Representation.BinaryOffender.IrrPlusFitting
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.GroupTheory.PGroup.SubnormalCore
/-!
# The actual actor of a normalized Section 12.2 choice

The original component acts on the chosen Irr⁺ subspace. Its action image is
nontrivial, and the normal two-core acts trivially because it centralizes the
reduced subgroup. Consequently the image is a quotient of the literal
`L / O₂(L)`, with the same central quotient when that source is quasisimple.
The two-group extension of this image is exactly the generalized Fitting
subgroup of the faithful seed actor. No representation type or ratio bound is
assumed here.

Source: Aschbacher--Smith, Theorem 12.2.2 (pp. 794--795), using the original
Irr⁺ selection and A.1.41.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

abbrev seedActor := subspaceActionImage (reducedRepresentation (L ⊔ (T : Subgroup G))) D.space
abbrev seedRepresentation : Representation (ZMod 2) D.seedActor D.space :=
  subspaceImageRepresentation (reducedRepresentation (L ⊔ (T : Subgroup G))) D.space
abbrev componentImage : Subgroup D.seedActor :=
  restrictedSubgroup (reducedRepresentation (L ⊔ (T : Subgroup G))) D.space
    (L.subgroupOf (L ⊔ (T : Subgroup G)))

def componentHom : L →* D.componentImage :=
  (restrictedActionSurjection (reducedRepresentation (L ⊔ (T : Subgroup G))) D.space
    (L.subgroupOf (L ⊔ (T : Subgroup G))) D.irrPlus.invariant).comp
      (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm.toMonoidHom

omit [Finite G] in
theorem componentHom_surjective : Function.Surjective D.componentHom :=
  (restrictedActionSurjection_surjective _ _ _ D.irrPlus.invariant).comp
    (subgroupOfEquivOfLe le_sup_left).symm.surjective

omit [Finite G] in
theorem componentImage_ne_bot : D.componentImage ≠ ⊥ :=
  restrictedSubgroup_ne_bot _ _ D.irrPlus.invariant (D.irrPlus.isIrrPlus.not_le_fixedSpace _)

omit [Finite G] in
instance componentImage_nontrivial : Nontrivial D.componentImage :=
  (Subgroup.nontrivial_iff_ne_bot D.componentImage).mpr D.componentImage_ne_bot

theorem componentHom_kills_core : pCore 2 L ≤ D.componentHom.ker := by
  let H := L ⊔ (T : Subgroup G)
  let : (L.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hc : L.pCoreIn 2 ≤ H.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn L H 2 le_sup_left
      (show (L.subgroupOf H).Normal from inferInstance).isSubnormal
  intro l hl
  apply Subtype.ext
  apply subspaceImageRepresentation_injective _ _
  ext v
  change (l : G) * (v.val.toMul.val : G) * (l : G)⁻¹ = (v.val.toMul.val : G)
  have hv : (v.val.toMul.val : G) ∈ V :=
    D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.property))
  have hh := D.core_centralizes (hc (mem_map_of_mem L.subtype hl))
    (v.val.toMul.val : G) hv
  change (v.val.toMul.val : G) * (l : G) = (l : G) * (v.val.toMul.val : G) at hh
  rw [← hh, mul_inv_cancel_right]

def componentQuotientHom : (L ⧸ pCore 2 L) →* D.componentImage :=
  QuotientGroup.lift _ D.componentHom D.componentHom_kills_core

theorem componentQuotientHom_mk (l : L) :
    D.componentQuotientHom (QuotientGroup.mk' (pCore 2 L) l) = D.componentHom l := by rfl

theorem componentQuotientHom_surjective : Function.Surjective D.componentQuotientHom :=
  QuotientGroup.lift_surjective_of_surjective (pCore 2 L) D.componentHom
    D.componentHom_surjective D.componentHom_kills_core

theorem componentImage_quasisimple (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    IsQuasisimple D.componentImage := by
  let := hq
  exact IsQuasisimple.of_surjective D.componentQuotientHom D.componentQuotientHom_surjective

def componentCentralQuotientEquiv (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      (D.componentImage ⧸ center D.componentImage) := by
  let := hq
  exact IsQuasisimple.centralQuotientEquiv D.componentQuotientHom
    D.componentQuotientHom_surjective

theorem seed_fitting (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    generalizedFitting D.seedActor = D.componentImage := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let := D.componentImage_quasisimple hq
  have hs : componentLayer D.componentImage = ⊤ := by
    apply top_unique
    exact le_sSup (show IsComponent D.componentImage ⊤ from
      ⟨(inferInstance : (⊤ : Subgroup D.componentImage).Normal).isSubnormal,
        IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  apply seed_image_fitting_of_shape _ X D.space D.irrPlus.isIrrPlus (Or.inl hs)
  apply isPGroup_quotient_of_sup_eq_top X ((T : Subgroup G).subgroupOf H)
    T.isPGroup'.comap_subtype
  rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
/-- The normalized source choice has its actual quasisimple component actor,
not a separately postulated faithful image or model equivalence. -/
theorem Hypothesis1221.exists_chosen_actor_of_normalizes
    (h : Hypothesis1221 K T L)
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ (V : Subgroup G) (D : ChosenModule T L V),
      generalizedFitting D.seedActor = D.componentImage ∧
      IsQuasisimple D.componentImage ∧
      Nonempty (((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
        (D.componentImage ⧸ center D.componentImage)) := by
  have hchoice : ∃ V : Subgroup G, Nonempty (ChosenModule T L V) :=
    h.exists_chosen_of_normalizes hn
  obtain ⟨V, hV⟩ := hchoice
  obtain ⟨D⟩ := hV
  exact ⟨V, D, D.seed_fitting h.quasisimple,
    D.componentImage_quasisimple h.quasisimple,
    ⟨D.componentCentralQuotientEquiv h.quasisimple⟩⟩
end CFSG.Quasithin.Chapter12.Section02
