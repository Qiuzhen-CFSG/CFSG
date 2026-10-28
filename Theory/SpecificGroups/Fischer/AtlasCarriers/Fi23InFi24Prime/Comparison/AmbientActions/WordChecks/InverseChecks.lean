module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.InverseChecks.A
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.InverseChecks.B
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.Reduction
public import Mathlib.Data.Fintype.EquivFin

/-!
# Global cancellation of the packed ambient letters

The two exhaustive numerical certificates give left inverses on all 306936
points. The `a` inverse table is definitionally its forward table; finiteness
turns the `b` left inverse into a right inverse. These facts discharge all four
signed letters and the cancellation premise of `inverse_wordMap_labelMap`.

The proof concerns the literal packed maps in `GeneratorData`, transcribed from
the retained ATLAS F24G1-p306936B0 tables. It needs no comparison with the
cycle-decoded carrier generators. Original data attribution is retained in
`AtlasCarriers/source/README.md`; see `InverseChecks/source/README.md` for the
certificate layout and measurements.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks

theorem aMap_right_inv (x : Fin 306936) : aMap (aInvMap x) = x :=
  aMap_left_inv x

theorem bMap_right_inv (x : Fin 306936) : bMap (bInvMap x) = x :=
  Function.LeftInverse.rightInverse_of_card_le bMap_left_inv (Nat.le_refl _) x

/-- Every packed letter cancels with the literal signed inverse letter. -/
theorem letterMap_inverse_apply (c : Fin 4) (x : Fin 306936) :
    letterMap (inverseLetter c) (letterMap c x) = x := by
  fin_cases c
  · exact aMap_left_inv x
  · exact bMap_left_inv x
  · exact aMap_right_inv x
  · exact bMap_right_inv x

/-- The actual short-word consumer, with numerical letter cancellation now
discharged. Forward-word agreement and its source-label right inverse remain
the separate word-certificate inputs. -/
theorem inverse_wordMap_labelMap_of_forward
    (ls : List (Fin 4)) (f g : Fin 31671 → Fin 31671)
    (hfg : ∀ i, f (g i) = i)
    (hf : ∀ i, wordMap letterMap false ls (labelMap i) = labelMap (f i))
    (i : Fin 31671) :
    wordMap letterMap true ls (labelMap i) = labelMap (g i) :=
  inverse_wordMap_labelMap letterMap_inverse_apply ls f g hfg hf i

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks
