module

public import Theory.SpecificGroups.SymmetricSix.MatchingEightGeneration
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme
public import Theory.Representation.BinaryAlternatingSixModels
import Mathlib.Tactic

/-!
# The diagram marking of the displayed matching eight-group

The existing exceptional automorphism sends the literal duad stabilizer to
the literal syntheme stabilizer. Transporting their intrinsic two-cores
therefore sends the coordinate product core to the matching group generated
by `(01)`, `(23)`, and `(45)`.

This is an explicit alternative quotient marking for the calculation after
Aschbacher--Smith (12.7.18), printed p.846. No identification with the action
on the six full-weight hexacode planes is asserted.
-/

public section
namespace Theory.SpecificGroups.SymmetricSix.MatchingEightGeneration
open Equiv Subgroup DuadCalculation SynthemeCalculation BinaryAlternatingSix

/-- The literal syntheme core is the displayed group of independent swaps. -/
theorem syntheme_core_eq_matching :
    (pCore 2 synthemeStabilizer).map synthemeStabilizer.subtype = matchingEight := by
  have hle : matchingEight ≤ (pCore 2 synthemeStabilizer).map synthemeStabilizer.subtype := by
    apply (closure_le _).mpr
    rintro _ (rfl | rfl | rfl)
    · refine ⟨⟨swap 0 1, by decide +kernel⟩, ?_, rfl⟩
      exact (mem_synthemeCore_iff_fix_blocks _).mpr (by decide +kernel)
    · refine ⟨⟨swap 2 3, by decide +kernel⟩, ?_, rfl⟩
      exact (mem_synthemeCore_iff_fix_blocks _).mpr (by decide +kernel)
    · refine ⟨⟨swap 4 5, by decide +kernel⟩, ?_, rfl⟩
      exact (mem_synthemeCore_iff_fix_blocks _).mpr (by decide +kernel)
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective synthemeStabilizer.subtype_injective,
    synthemeCore_card, matching_card.1]

/-- The marked exceptional automorphism sends the full duad core to the
matching eight-group, retaining both literal embeddings. -/
theorem diagram_productCore_eq_matching :
    (productCore.map duadProductHom).map diagramAut.toMonoidHom = matchingEight := by
  let e : duadStabilizer ≃* synthemeStabilizer := {
    toFun := fun g => ⟨diagramAut g.val, (diagramAut_mem_syntheme g.val).mpr g.property⟩
    invFun := fun g => ⟨diagramAut.symm g.val,
      (diagramAut_mem_syntheme _).mp (by simp [g.property])⟩
    left_inv := fun g => Subtype.ext (diagramAut.symm_apply_apply g.val)
    right_inv := fun g => Subtype.ext (diagramAut.apply_symm_apply g.val)
    map_mul' := fun g h => Subtype.ext (map_mul diagramAut g.val h.val) }
  have hcomp : diagramAut.toMonoidHom.comp duadProductHom =
      synthemeStabilizer.subtype.comp (e.toMonoidHom.comp duadProductEquiv.toMonoidHom) := rfl
  rw [map_map, hcomp, ← map_map, ← map_map, productCore_eq,
    pCore_map_iso, pCore_map_iso, syntheme_core_eq_matching]

/-- The exceptional diagram marking preserves evenness exactly. -/
theorem diagram_sign_eq_one_iff (g : S6) :
    (diagramAut g).sign = 1 ↔ g.sign = 1 := by
  constructor
  · intro hg
    let a : A6 := ⟨diagramAut g, hg⟩
    have he : ((alternatingDiagramAut.symm a).val : S6) = g := by
      apply diagramAut.injective
      rw [← alternatingDiagramAut_coe, alternatingDiagramAut.apply_symm_apply]
    exact he ▸ (alternatingDiagramAut.symm a).property
  · intro hg
    exact (alternatingDiagramAut (⟨g, hg⟩ : A6)).property

end Theory.SpecificGroups.SymmetricSix.MatchingEightGeneration
