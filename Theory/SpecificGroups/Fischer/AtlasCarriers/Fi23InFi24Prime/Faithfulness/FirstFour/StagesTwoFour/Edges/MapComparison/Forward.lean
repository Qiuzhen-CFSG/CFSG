module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Soundness

/-!
# Forward comparison through the existing staged certificates

The cached forward tables for words 11, 14, 17 and 20 are definitionally the
same as the independently published intermediate tables. Reusing their staged
cross-composition proofs avoids expanding the enormous original words at every
point. The four later tables are aliases interpreted by `TableAgreement`.
The seed and middle numerical certificates still require their existing producers.
Source: the literal `FirstFour.Words`, ATLAS F24G1-p306936B0, GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges.MapComparison
open LastFour.Transitions

/-- Both encodings select the same packed block, with the same bit convention. -/
theorem forward11_eq : Tables.Word11.forward = Staged.raw11 := by rfl

theorem forward14_eq : Tables.Word14.forward = Staged.raw14 := by rfl

theorem forward17_eq : Tables.Word17.forward = Staged.raw17 := by rfl

theorem forward20_eq : Tables.Word20.forward = Staged.raw20 := by rfl

/-- All eight positive comparisons, retaining the independent finite certificates. -/
theorem forward_of_stagedChecks (hs : Staged.SeedChecks) (hm : Staged.MiddleChecks)
    (hl : TableAgreement) : ∀ (i : Fin 8) (x : Fin 306936),
    cachedMaps i true x.val = (literal i x).val := by
  obtain ⟨c5, c8⟩ := hs
  obtain ⟨c11, c14, c17, c20⟩ := hm
  have h5 := Staged.agrees5 c5
  have h8 := Staged.agrees8 c8
  have h11 := Staged.agrees11 h5 h8 c11
  have h14 := Staged.agrees14 h5 h8 c14
  have h17 := Staged.agrees17 h11 h14 c17
  have h20 := Staged.agrees20 h11 h14 c20
  intro i x
  fin_cases i <;> simp only [cachedMaps, literal, ↓reduceIte] <;> dsimp only [Ambient]
  · have hx := (h11 x).symm
    rw [forward11_eq]
    exact hx
  · have hx := (h14 x).symm
    rw [forward14_eq]
    exact hx
  · have hx := (h17 x).symm
    rw [forward17_eq]
    exact hx
  · have hx := (h20 x).symm
    rw [forward20_eq]
    exact hx
  · have hx := (hl 0 0 x).symm
    exact hx
  · have hx := (hl 0 1 x).symm
    exact hx
  · have hx := (hl 0 2 x).symm
    exact hx
  · have hx := (hl 0 3 x).symm
    exact hx

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges.MapComparison
