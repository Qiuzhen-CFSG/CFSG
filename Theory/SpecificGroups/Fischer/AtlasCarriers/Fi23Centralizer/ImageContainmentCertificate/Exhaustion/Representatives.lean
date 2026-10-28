module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.FixedPointSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.WordData

/-!
# Actual Fi23 words for the exhaustion certificate

Every representative is a word in the two literal ATLAS generators, hence is
an element of the original carrier without any computed membership premise.
The base representative is the identity. The Schreier edges use the actual
generator actions on the original labels; no conjugation model is assumed.

Source: ATLAS F23G1-p31671B0, GLS3 Table 5.3u. The reproducible word search is
in `Exhaustion/source/`; it supplies data, not proofs of edge membership.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion

def base : Fin 31671 := 15181

def letter (b : Bool) : Carrier := if b then CentralizerSection.b else a

theorem inclusion_letter_false : inclusion (letter false) = generatorA := rfl

theorem inclusion_letter_true : inclusion (letter true) = generatorB := rfl

def representative (x : Fin 31671) : Carrier :=
  (((wordCode x).bits.dropLast).map letter).prod

theorem representative_base : representative base = 1 := by
  have hc : wordCode base = 1 := by decide +kernel
  simp [representative, hc]

/-- The literal left Schreier edge, as an actual element of Fi23. -/
def edge (b : Bool) (x : Fin 31671) : Carrier :=
  (representative (inclusion (letter b) x))⁻¹ * letter b * representative x

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion
