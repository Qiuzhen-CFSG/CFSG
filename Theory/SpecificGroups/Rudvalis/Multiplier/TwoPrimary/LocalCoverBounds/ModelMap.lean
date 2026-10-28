module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.Presentation
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.Definitions
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Comparison
public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase

/-!
# The literal map from the seven-relator group to Rudvalis max4

The original two ATLAS generators satisfy each candidate relator, checked on
five points. They generate the literal subgroup by definition, so the resulting
map from the presented group is surjective and preserves the marked generator.
Injectivity remains an independent presentation-completeness obligation.

Source: Aschbacher--Smith I.1.3(1), p.407; ATLAS words and conventions are
attributed in `SylowOvergroups.Definitions` and `LocalCoverBounds/source`.
-/

@[expose] public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation
open SylowOvergroups

/-- The original generators, with no change of marking. -/
def modelGenerator : Bool → max4
  | false => max4First
  | true => ⟨max4Generators.2, Subgroup.subset_closure (by simp)⟩

set_option maxRecDepth 10000 in
private theorem concrete_relations : ∀ j : Fin 7,
    ∀ i : Fin 5, word (LocalCardinality.Max4.L0.gen 0)
      (LocalCardinality.Max4.L0.gen 1) j (i.castLE (by decide)) = i.castLE (by decide) := by
  decide +kernel

/-- Each relation holds in the actual subgroup, using its certified five-point base. -/
theorem modelGenerator_word (j : Fin 7) :
    word (modelGenerator false) (modelGenerator true) j = 1 := by
  apply Subtype.ext
  change max4.subtype (word (modelGenerator false) (modelGenerator true) j) = 1
  rw [map_word]
  apply eq_of_smul_first_five
  intro i
  change modelSubgroup.subtype (word max4Generators.1 max4Generators.2 j)
    (i.castLE (by decide)) = i.castLE (by decide)
  erw [map_word]
  rw [← LocalCardinality.Max4.generator0_eq, ← LocalCardinality.Max4.generator1_eq]
  exact concrete_relations j i

def modelEvaluation : Free →* max4 := FreeGroup.lift modelGenerator

theorem modelEvaluation_relator (i : Fin 7) : modelEvaluation (relator i) = 1 := by
  simpa only [modelEvaluation, relator, map_word, FreeGroup.lift_apply_of] using
    modelGenerator_word i

/-- A surjection onto max4; faithfulness is not asserted in this module. -/
def modelMap : Presented →* max4 :=
  PresentedGroup.toGroup (f := modelGenerator) (by
    rintro _ ⟨i, rfl⟩
    exact modelEvaluation_relator i)

@[simp] theorem modelMap_toPresented (x : Free) : modelMap (toPresented x) = modelEvaluation x :=
  rfl

@[simp] theorem modelMap_generator (i : Bool) : modelMap (generator i) = modelGenerator i :=
  FreeGroup.lift_apply_of

/-- The literal first generator of the presentation maps to the required marker. -/
theorem modelMap_first : modelMap (generator false) = max4First := modelMap_generator false

theorem modelMap_surjective : Function.Surjective modelMap := by
  rw [← MonoidHom.range_eq_top]
  have hle : max4 ≤ modelMap.range.map max4.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · exact ⟨modelGenerator false, ⟨generator false, modelMap_generator false⟩, rfl⟩
    · exact ⟨modelGenerator true, ⟨generator true, modelMap_generator true⟩, rfl⟩
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  exact (Subtype.ext he : y = x) ▸ hy

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation
