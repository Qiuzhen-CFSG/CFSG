module

public import Stellmacher.Recognition.Parrott.BraidOrderAlternatives
public import Stellmacher.Recognition.Parrott.BraidReduction
public import Theory.SpecificGroups.Tits.RecognitionBraidWords

/-!
# Parrott's eighth-power braid relation

The compatible local generators satisfy VI(i), (rs)⁸ = 1. The two involution
centralizers give the alternatives (rs)⁸ = 1 or (rs)¹⁰ = 1. In the latter
case, the fourth-power conjugation identity and nonconjugacy of r and s force
order ten. Fusion in the second centralizer places r in O₂(C_G((rs)⁵r)).
The local word identities then make a fourth power in a two-group conjugate
to (sr)⁴, an element of order five, giving a contradiction.

All word identities and centralizer inputs are discharged for the same
supplied compatible pair. Combining VI(i) with the 36 local relators gives
the full presentation on its existing generator words. Construction of the
ambient presentation realization remains with the recognition theorem.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§6, printed p.684, Verification of VI(i), including equation (*).
-/

namespace Stellmacher.Recognition.ParrottNormalizerGeneratorData

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)

/-- Relation VI(i) holds for the same compatible generators used by the
36 local relators, with all order and word-identity inputs discharged. -/
public theorem braid_eighth_power
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
    (f.r * k.s) ^ 8 = 1 := by
  exact k.braid_eighth_power_of_local_steps h (n.second_centralizer_data h hN)
    k.localRelations.braid_fourth_conjugation
    k.localRelations.braid_ten_commute
    (fun _ => k.localRelations.braid_word_fourth_power)
    (k.braid_order_alternatives h hN)

/-- All 37 Parrott relators hold on the existing compatible generator words. -/
public theorem satisfiesParrottRelations
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
    Tits.SatisfiesParrottRelations k.words := by
  apply (Tits.satisfiesParrottRelations_iff_except_braid k.words).mpr
  exact ⟨k.relators_except_braid, k.braid_eighth_power h hN⟩

end Stellmacher.Recognition.ParrottNormalizerGeneratorData
