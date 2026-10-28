module
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions.KnownSimpleSource
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs

/-!
# The original single-component carrier catalogue in G.9

The simple central quotient of the component is an actual semisimple section
of the given SQTK cover. The completed Theorem A bounds its odd ranks and
Theorem C supplies its full model. Faithful irreducibility kills the ambient
two-core, so the completed ordinary A.3.6 theorem classifies the original
component itself. Quasisimplicity excludes both solvable-Fitting alternatives.

The conclusion retains the literal component and its central three-cover;
it is the carrier input for the separate G.9 action and degree arguments.
Source: Aschbacher--Smith G.9.3, p.356; A.2.1--3 and A.3.6, pp.33--45.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterG.Section09
open Chapter1.Section02
open TwoComponents.FactorReduction.ModelRestrictions
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A L H : Subgroup G} {m : ℕ}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem ambient_irreducible
    (hi : IsIrreducible (ρ.comp L.subtype)) : IsIrreducible ρ := by
  let := hi
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp L.subtype)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let U : Subrepresentation (ρ.comp L.subtype) :=
    ⟨S.toSubmodule, fun e _ hv => S.apply_mem_toSubmodule (e : G) hv⟩
  rcases eq_bot_or_eq_top U with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun W : Subrepresentation (ρ.comp L.subtype) => W.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun W : Subrepresentation (ρ.comp L.subtype) => W.toSubmodule) h

/-- The exhaustive original carrier alternatives with the full known-simple
class and all earlier Theorem A/C/A.3.6 premises discharged. -/
theorem ComponentHypothesis.single_component_models
    (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ A L L m) :
    (IsSimpleGroup L ∧ LocalModels.TheoremCModel L) ∨
      (Nonempty (center L ≃* Multiplicative (ZMod 3)) ∧ LocalModels.ThreeCoverModel L) := by
  let : IsQuasisimple L := h.component.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsQuasisimple (L ⧸ center L) :=
    IsQuasisimple.of_surjective (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
  have hsemi : ChapterA.Section02.IsSemisimple (L ⧸ center L) := by
    apply top_unique
    exact le_sSup (show IsComponent (L ⧸ center L) ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  obtain ⟨c⟩ := h.quotient
  have hsec := (ChapterA.Section02.IsSectionOf.quotient_subgroup L (center L)).ambient_surjective
    c.projection c.surjective
  have hsq := semisimpleSectionRank_knownSimple c.Cover c.sqtk _ hsec hsemi
  have hna := Group.IsPerfect.not_isMulCommutative (L ⧸ center L)
  have hm := ChapterA.Section02.theoremC_knownSimple inferInstance hna hsq
    ((c.isKGroup.subgroup L).quotient (center L))
  let : IsIrreducible ρ := ambient_irreducible h.irreducible
  have hs := ChapterA.SQTKStructure.OrdinarySource.ordinary_conclusion_of_model
    h.toSetup.twoCore_eq_bot L h.component
    (ChapterA.Section03.SourceComponents.sourceTheoremC_to_local hna hm)
  have hfit : generalizedFitting L ≠ fittingSubgroup L := by
    intro he
    have hf : fittingSubgroup L = ⊤ := he.symm.trans generalizedFitting_eq_top_of_quasisimple
    let : Group.IsSolvable (⊤ : Subgroup L) := hf ▸
      (inferInstance : Group.IsSolvable (fittingSubgroup L))
    exact h.component.isCComponent.not_isSolvable
      (Group.isSolvable_of_surjective (f := (topEquiv (G := L)).toMonoidHom)
        (topEquiv (G := L)).surjective)
  cases hs.1 with
  | simple _ hi hm => exact .inl ⟨hi,hm⟩
  | cover _ hc hm => exact .inr ⟨hc,hm⟩
  | natural he => exact (hfit he.1).elim
  | nilpotent he => exact (hfit he.1).elim

end CFSG.Quasithin.ChapterG.Section09
