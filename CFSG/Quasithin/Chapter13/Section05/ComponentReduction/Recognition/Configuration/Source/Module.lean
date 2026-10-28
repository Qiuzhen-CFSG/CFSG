module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.SourceDefs
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Commutator

/-!
# Original condition (iii) of the13.5.21 configuration

Both existing faithful-action constructions agree on every original quotient
representative. The proved F.9.5(2) identity gives the moved seed, its order
four gives dimension two, and the original seed commutator with L₁ supplies
the second commutator identity. No replacement representation is chosen.
Source: Aschbacher–Smith13.5.21(iii), printed p.923.
-/
public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include h

/-- Equality on the original quotient representatives identifies the two APIs. -/
theorem sourceRepresentation_eq : Action.starRepresentation D h = Fitting.SourceAction.representation h := by
  apply MonoidHom.ext
  intro x
  apply LinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D.H) x
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (D.V₁.subgroupOf D.UH) v.toMul
  have hv := congrArg Additive.ofMul hu
  change Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) = v at hv
  rw [←hv,Action.starRepresentation_apply,Fitting.SourceAction.representation_apply]

/-- The original seed commutator passes through the literal action and quotient. -/
theorem seedSpace_local_commutator
    (hc : D.Vplus = ⁅D.Vplus,D.L₁⁆) :
    subspaceCommutator (Action.starRepresentation D h) (Action.seedSpace D)
      (starImage D.H D.L₁) = Action.seedSpace D := by
  let q := QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
  have hLH : D.L₁ ≤ D.H := le_sup_left.trans h.local_le
  let f := (QuotientGroup.mk' (pCore 2 D.H)).comp (inclusion hLH)
  have hr : f.range = starImage D.H D.L₁ := by
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact mem_map_of_mem _ l.property
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  have he := quotientImage_commutator (Action.starRepresentation D h) D.UH D.Vplus D.L₁
    (hLH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H))
    (le_conjugateSpanBy _ _) f q (QuotientGroup.mk'_surjective _)
    (fun x u => Action.starRepresentation_apply D h (inclusion hLH x) u)
  rw [hr,←hc] at he
  exact he.symm

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- All of source condition(iii) on the exact marked action. -/
theorem source_module_conditions
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hc : Nat.card D.V = 16) (hl : D.Vplus = ⁅D.Vplus,D.L₁⁆) : ModuleConditions D h := by
  let := Action.point_normal D h
  let := Action.quotient_elementary D h
  refine ⟨?_,seedSpace_local_commutator h hl,?_⟩
  · rw [sourceRepresentation_eq h]
    exact Fitting.SourceAction.moved_space_eq_seed h Fitting.SourceAction.source_F95Two hi hu
  · have hr := Fitting.SourceAction.source_fixedCodim_two h hi hu hc
    rw [Fitting.SourceAction.fixedCodim_eq_moved_finrank_of_card_two _ _
      (LocalGeometry.star_V_card_two h hi hu),
      Fitting.SourceAction.moved_space_eq_seed h Fitting.SourceAction.source_F95Two hi hu] at hr
    exact hr
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
