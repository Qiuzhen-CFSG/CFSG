module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor
public import Theory.Representation.BinaryOffender.IrreducibleDiagonal
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.SourceBounds
/-!
# SQTK and irreducibility for the original seed actor

The component action is a genuine semisimple section of the original local
SQTK group. Theorem A transfers the odd-prime rank bound to that section;
the remaining quotient is a two-group, so the faithful stabilizer image is
SQTK. This uses the actual known-simple catalogue when applied to Chapter K.
If V intersects its L-centralizer trivially, its Irr⁺ action is irreducible.
These facts construct the literal SourceAction used by the existing degree
bounds, rather than postulating its group or representation hypotheses.

Source: Aschbacher--Smith, A.2.1, D.3.4 and the proof of 12.2.2,
pp.33, 194 and 794--795. The full module classification is not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem irreducible_of_irrPlus_fixed_bot {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) A W)
    (X : Subgroup A) (hI : IsIrrPlus ρ X ⊤) (hc : fixedSpace ρ X = ⊥) :
    Representation.IsIrreducible (ρ.comp X.subtype) := by
  let : Nontrivial (⊤ : Submodule (ZMod 2) W) :=
    Submodule.nontrivial_iff_ne_bot.mpr (hI.ne_bot ρ)
  let : Nontrivial W := (⊤ : Submodule (ZMod 2) W).subtype_injective.nontrivial
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  have hS : X ≤ subspaceStabilizer ρ S.toSubmodule :=
    le_subspaceStabilizer ρ S.toSubmodule (fun x hx v hv =>
      S.apply_mem_toSubmodule ⟨x, hx⟩ hv)
  rcases hI.le_or_inf_sup_fixedSpace_le ρ hS with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact top_unique h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact bot_unique (by simpa only [hc, sup_bot_eq, top_inf_eq] using h)

omit [Finite G] in
theorem seed_fixedSpace_eq_bot (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    fixedSpace D.seedRepresentation D.componentImage = ⊥ := by
  rw [fixedSpace_restrictedSubgroup _ _ _ D.irrPlus.invariant]
  apply bot_unique
  intro v hv
  have hvV : (v.val.toMul.val : G) ∈ V :=
    D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.property))
  have hvC : (v.val.toMul.val : G) ∈ centralizer (L : Set G) := by
    intro l hl
    have he := congrArg (fun w : Additive (ReducedModule (L ⊔ (T : Subgroup G))) =>
      (w.toMul.val : G)) (hv ⟨⟨l, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hl⟩, hl⟩)
    change l * (v.val.toMul.val : G) * l⁻¹ = (v.val.toMul.val : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have he : (v.val.toMul.val : G) = 1 := hc.le ⟨hvV, hvC⟩
  exact Subtype.ext (Additive.toMul.injective (Subtype.ext (Subtype.ext he)))

omit [Finite G] in
theorem seed_irreducible (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    Representation.IsIrreducible (D.seedRepresentation.comp D.componentImage.subtype) := by
  apply irreducible_of_irrPlus_fixed_bot D.seedRepresentation D.componentImage _
    (D.seed_fixedSpace_eq_bot hc)
  simpa only [Submodule.comap_subtype_self] using
    D.irrPlus.isIrrPlus.restricted (reducedRepresentation (L ⊔ (T : Subgroup G)))
      D.irrPlus.invariant le_rfl
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L V : Subgroup G}

theorem Hypothesis1221.join_sqtk (h : Hypothesis1221 K T L) :
    IsSQTK K (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let H := L ⊔ (T : Subgroup G)
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal N :=
    ⟨R, h.maximal_faithful.1.1.2.2, isPGroup_pCoreIn 2 H, rfl⟩
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((h.simpleQTKE.twoLocal_sqtk hN).subgroup (H.subgroupOf N))

namespace ChosenModule
variable (D : ChosenModule T L V)

instance componentImage_normal : D.componentImage.Normal := by
  let H := L ⊔ (T : Subgroup G)
  let : (L.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  exact Normal.map inferInstance (subspaceActionHom (reducedRepresentation H) D.space)
    (stabilizerRepresentation (reducedRepresentation H) D.space).asGroupHom.rangeRestrict_surjective

omit [Finite G] in
theorem seed_quotient_isTwoGroup : IsPGroup 2 (D.seedActor ⧸ D.componentImage) := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let ρ := reducedRepresentation H
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hp : IsPGroup 2 (H ⧸ X) := by
    apply isPGroup_quotient_of_sup_eq_top X ((T : Subgroup G).subgroupOf H)
      T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  let A := subspaceStabilizer ρ D.space
  let f := subspaceActionHom ρ D.space
  have hf : Function.Surjective f :=
    (stabilizerRepresentation ρ D.space).asGroupHom.rangeRestrict_surjective
  have hpA : IsPGroup 2 (A ⧸ X.subgroupOf A) :=
    (hp.to_subgroup (A.map (QuotientGroup.mk' X))).of_equiv
      (quotientSubgroupRangeEquiv A X).symm
  have hx : X.subgroupOf A ≤ D.componentImage.comap f := fun x hx => mem_map_of_mem f hx
  exact hpA.of_surjective (QuotientGroup.map _ _ f hx)
    (QuotientGroup.map_surjective_of_surjective _ _ f
      ((QuotientGroup.mk'_surjective _).comp hf) hx)

theorem seed_sqtk (h : Hypothesis1221 K T L)
    (hA : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremA K X) :
    IsSQTK K D.seedActor := by
  let H := L ⊔ (T : Subgroup G)
  have hH := h.join_sqtk
  have hL : IsSQTK K L := (IsSQTK.equiv (subgroupOfEquivOfLe
    (show L ≤ H from le_sup_left))).mp (hH.subgroup (L.subgroupOf H))
  let := D.componentImage_quasisimple h.quasisimple
  have hs : ChapterA.Section02.IsSemisimple D.componentImage := by
    apply top_unique
    exact le_sSup (show IsComponent D.componentImage ⊤ from
      ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hS := (hA L).stronglyQuasithin_section hL.stronglyQuasithin hL.isKGroup
    (ChapterA.Section02.IsSectionOf.of_surjective D.componentHom D.componentHom_surjective) hs
  refine ⟨ChapterB.QuasisimpleSource.IrreducibleBranch.stronglyQuasithin_of_twoGroup_quotient
    D.componentImage D.seed_quotient_isTwoGroup hS, ?_⟩
  exact (hH.isKGroup.subgroup (subspaceStabilizer (reducedRepresentation H) D.space)).of_surjective
    (subspaceActionHom (reducedRepresentation H) D.space)
    (stabilizerRepresentation (reducedRepresentation H) D.space).asGroupHom.rangeRestrict_surjective
end ChosenModule
end CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
theorem seed_source_action (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) : SourceAction D.seedRepresentation := by
  refine ⟨D.seed_sqtk h hA, ?_, subspaceImageRepresentation_injective _ _, ?_⟩
  · rw [D.seed_fitting h.quasisimple]
    exact D.componentImage_quasisimple h.quasisimple
  · exact (congrArg (fun X : Subgroup D.seedActor =>
      Representation.IsIrreducible (D.seedRepresentation.comp X.subtype))
        (D.seed_fitting h.quasisimple)).mpr (D.seed_irreducible hc)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
