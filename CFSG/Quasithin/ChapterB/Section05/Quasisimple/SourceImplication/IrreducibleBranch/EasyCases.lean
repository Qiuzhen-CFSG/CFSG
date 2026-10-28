module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalClassification
public import Theory.Representation.BinaryOffender.RestrictionComparison

/-!
# The ratio-one and zero-central-kernel cases of B.5.1

Suppose the offender subgroup of LT on S=[V,L]/C_[V,L](L) is L.
At ratio one, every original offender in T is a best offender on S.
When C_[V,L](L)=0, restriction preserves best-offender weight comparisons.
In either case all those offenders lie in L, so source observation α gives G=L.
We then construct the full corrected irreducible alternative on the actual S.

The final reduction retains the complete corrected local catalogue and exposes
exactly the two remaining source branches: a proper outer offender group, or
a nonzero central kernel with quotient ratio strictly below one. It does not
prove those branches or the complete B.5.1 theorem. Its only source parameter
is the full corrected B.4.2 input; SQTK inheritance also uses the explicit
ContainsSimpleTwoGroups K class condition.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed pp.99–100, through the start of the final irreducible-branch paragraph.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Source α closes the J=L branch when the local quotient ratio is one. -/
theorem whole_of_local_ratio_one [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    (hJ : offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) =
      L.subgroupOf (L ⊔ (T : Subgroup G)))
    (hq : quadraticRatio (s.action.comp (L ⊔ (T : Subgroup G)).subtype) = 1) : L = ⊤ := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  apply whole_of_sylow_offenders_le ρ L T h.generated
  apply iSup₂_le
  intro B hB
  have hBD : B ≤ L ⊔ (T : Subgroup G) := hB.2.trans le_sup_right
  have ho := moved_offender s (hB.1.isOffender ρ)
  have hl : IsOffender (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
      (B.subgroupOf (L ⊔ (T : Subgroup G))) := by
    refine ⟨(hB.1.subgroupOf ρ hBD).1, ?_⟩
    have he : fixedCodim (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
        (B.subgroupOf (L ⊔ (T : Subgroup G))) = fixedCodim s.action B := by
      unfold fixedCodim
      rw [Representation.BinaryOffender.fixedSpace_comp_map,
        map_subgroupOf_eq_of_le hBD]
    have hr := rank_map_injective (L ⊔ (T : Subgroup G)).subtype
      Subtype.val_injective (B.subgroupOf (L ⊔ (T : Subgroup G)))
    rw [map_subgroupOf_eq_of_le hBD] at hr
    rw [he, ← hr]
    exact ho.2
  have hb := (hl.best_and_codim_eq_of_quadraticRatio_eq_one _ hq).1
  have hle : B.subgroupOf (L ⊔ (T : Subgroup G)) ≤
      offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) :=
    le_iSup_of_le _ (le_iSup_of_le ⟨hb, le_top⟩ le_rfl)
  rw [hJ] at hle
  intro b hb
  exact hle (show (⟨b, hBD hb⟩ : ↥(L ⊔ (T : Subgroup G))) ∈
    B.subgroupOf (L ⊔ (T : Subgroup G)) from hb)

/-- With zero central kernel, restriction preserves every original best offender. -/
theorem moved_bestOffender_of_central_eq_bot [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) (hc : s.central.toSubmodule = ⊥)
    {A : Subgroup G} (hA : IsBestOffender ρ A) : IsBestOffender s.action A := by
  have hb : IsBestOffender s.space.toRepresentation A := by
    refine ⟨hA.1, fun B hBA => ?_⟩
    have hle := hA.restriction_weight_le ρ hBA s.space.toSubmodule
    unfold weight
    rw [(subrepresentationFixedEquiv ρ s.space B).finrank_eq,
      (subrepresentationFixedEquiv ρ s.space A).finrank_eq]
    exact hle
  let e := (s.central.toSubmodule.quotEquivOfEqBot hc).symm
  have he (B : Subgroup G) :
      (fixedSpace s.space.toRepresentation B).map e.toLinearMap = fixedSpace s.action B := by
    have hh := fixedSpace_map_equivariant s.space.toRepresentation s.action
      (MonoidHom.id G) e (fun _ _ => rfl) B
    simpa only [Subgroup.map_id] using hh
  have hw (B : Subgroup G) : weight s.action B = weight s.space.toRepresentation B := by
    unfold weight
    rw [← he, e.finrank_map_eq]
  refine ⟨hb.1, fun B hBA => ?_⟩
  rw [hw, hw]
  exact hb.2 B hBA

/-- Source α closes the J=L branch when the moved central kernel is zero. -/
theorem whole_of_central_eq_bot [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    (hJ : offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) =
      L.subgroupOf (L ⊔ (T : Subgroup G)))
    (hc : s.central.toSubmodule = ⊥) : L = ⊤ := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  apply whole_of_sylow_offenders_le ρ L T h.generated
  apply iSup₂_le
  intro B hB
  have hBD : B ≤ L ⊔ (T : Subgroup G) := hB.2.trans le_sup_right
  have hb := (moved_bestOffender_of_central_eq_bot s hc hB.1).subgroupOf s.action hBD
  have hle : B.subgroupOf (L ⊔ (T : Subgroup G)) ≤
      offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) :=
    le_iSup_of_le _ (le_iSup_of_le ⟨hb, le_top⟩ le_rfl)
  rw [hJ] at hle
  intro b hb
  exact hle (show (⟨b, hBD hb⟩ : ↥(L ⊔ (T : Subgroup G))) ∈
    B.subgroupOf (L ⊔ (T : Subgroup G)) from hb)

/-- When G=L, construct every datum of the corrected irreducible B.5.1 alternative. -/
theorem irreducible_case_of_whole [Finite G] {K : CFSG.Quasithin.GroupClass}
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u, v} K)
    (hK : ContainsSimpleTwoGroups K)
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hI : IsIrrPlus ρ L s.space.toSubmodule) (hL : L = ⊤) :
    L = generalizedFitting G ∧ SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s := by
  let T : Sylow 2 G := Classical.choice inferInstance
  obtain ⟨hfit, hfaith, hcase⟩ := ambient_classification_of_local_eq_top earlier hK h s hI
    T T.isPGroup' (by rw [hL, top_sup_eq])
  exact ⟨hfit, .irreducible hI hfaith (moved_action_irreducible s hI) hcase (Or.inl hL)⟩

/-- All unresolved source work is in the outer-action and the nonsplit,
strictly-small-ratio branches. The full local catalogue accompanies both. -/
theorem irreducible_branch_reduction [Finite G] {K : CFSG.Quasithin.GroupClass}
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u, v} K)
    (hK : ContainsSimpleTwoGroups K)
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hI : IsIrrPlus ρ L s.space.toSubmodule) (T : Sylow 2 G) :
    (L = generalizedFitting G ∧ SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) ∨
    (SourceInduction.ProjectiveLine.IrreducibleActionCase
        (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
        (generalizedFitting ↥(L ⊔ (T : Subgroup G)))
        (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype)) ∧
      (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) ≠
          L.subgroupOf (L ⊔ (T : Subgroup G)) ∨
        (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) =
            L.subgroupOf (L ⊔ (T : Subgroup G)) ∧
          s.central.toSubmodule ≠ ⊥ ∧
          quadraticRatio (s.action.comp (L ⊔ (T : Subgroup G)).subtype) < 1))) := by
  classical
  let := h.finite_module
  by_cases hJ : offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) =
      L.subgroupOf (L ⊔ (T : Subgroup G))
  · by_cases hc : s.central.toSubmodule = ⊥
    · exact Or.inl (irreducible_case_of_whole earlier hK h s hI
        (whole_of_central_eq_bot h s T hJ hc))
    by_cases hq : quadraticRatio (s.action.comp (L ⊔ (T : Subgroup G)).subtype) = 1
    · exact Or.inl (irreducible_case_of_whole earlier hK h s hI
        (whole_of_local_ratio_one h s T hJ hq))
    obtain ⟨B, hB⟩ := local_bestOffender h s T
    have hle := (isFFModule_iff_quadraticRatio_le_one _).mp ⟨B, hB.isOffender _⟩
    exact Or.inr ⟨local_classification earlier hK h s hI T,
      Or.inr ⟨hJ, hc, lt_of_le_of_ne hle hq⟩⟩
  · exact Or.inr ⟨local_classification earlier hK h s hI T, Or.inl hJ⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
