module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.FourSpace.Coordinates
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings

/-!
# The natural linear normalizer of A₆

The faithful natural S₆ action normalizes its alternating image and has
order 720. Transporting that image through the actual GL₄(2) ≃ A₈ comparison
identifies it as an even pointwise pair stabilizer, whose normalizer has
order at most 720. Containment and cardinality give equality with the
literal symmetric image in `Six.Inputs`.

This discharges the normalizer premise used by `six_extension_of_normalizer`
to recover the marked ambient S₆ extension. Source: Aschbacher–Smith,
K.1–K.1.1, printed p.452 (PDF p.463). The imported exceptional comparison
retains the ATLAS attribution and license in its owning modules.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six

/-- Symmetric operators normalize the image of the alternating subgroup. -/
theorem natural_range_le_normalizer :
    naturalLinearAction.range ≤ normalizer (alternatingLinearImage : Set _) := by
  change naturalLinearAction.range ≤ normalizer
    ((naturalLinearAction.comp (alternatingGroup (Fin 6)).subtype).range : Set _)
  rw [MonoidHom.range_comp, range_subtype]
  have h := Subgroup.le_normalizer_map (H := alternatingGroup (Fin 6)) naturalLinearAction
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map] using h

/-- The full linear normalizer is precisely the literal natural S₆ image. -/
theorem normalizer : Normalizer := by
  let e := naturalLinearEquivAlternatingEight
  let : Finite (BinaryPermutation.natural (Fin 6) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin 6)) := Finite.of_injective e e.injective
  let f := e.toMonoidHom.comp
    (naturalLinearAction.comp (alternatingGroup (Fin 6)).subtype)
  have hf : Function.Injective f := e.injective.comp natural_alternating_action_injective
  have hr : f.range = alternatingLinearImage.map e.toMonoidHom := MonoidHom.range_comp _ _
  have hn := Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.normalizer_card_le f hf
  rw [hr, ← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective e.injective] at hn
  have hs : Nat.card naturalLinearAction.range = 720 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective six_naturalLinearAction_injective).toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  exact (Subgroup.eq_of_le_of_card_ge natural_range_le_normalizer (by omega)).symm

end CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six
