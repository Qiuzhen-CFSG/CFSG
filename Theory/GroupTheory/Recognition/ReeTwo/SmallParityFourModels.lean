module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourCoordinates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourFirstCounts
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourFrattini
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourLastCounts

/-!
# Assembly of the eight rank-four Frattini models

The coordinate sections supply surjectivity on the exact candidate subgroups.
Multiplicativity, the Frattini identity fiber, and the intrinsic counts are
separate certificates. This interface assembles them without choosing new
coordinates or changing the profile basis.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified root model;
see `SmallParityFourCoordinates` and `SmallParityProfiles`.
-/

namespace ReeTwo.SylowModel

/-- Assemble a model from the algebraic and counting certificates for the fixed coordinates. -/
public theorem smallParityFourFrattiniModel_of_certificates (i : Fin 8)
    (hmul : ∀ x y, smallParityFourMap i (x * y) =
      smallParityFourMap i x * smallParityFourMap i y)
    (hker : ∀ x, smallParityFourMap i x = 1 ↔
      x ∈ frattini (smallParityTwoCandidate (smallParityFourIndex i)))
    (hcounts : ∀ v, smallParityFourCoordinateProfile i v = smallParityFourProfile i v) :
    SmallParityFourFrattiniModel i := by
  let π : smallParityTwoCandidate (smallParityFourIndex i) →* SmallParityFourQuotient :=
    MonoidHom.mk' (smallParityFourMap i) hmul
  refine ⟨π, smallParityFourMap_surjective i, ?_, ?_⟩
  · ext x
    exact hker x
  · exact hcounts

/-- The algebra and intrinsic-count certificates realize all eight rank-four models. -/
public theorem smallParityFourFrattiniModels :
    ∀ i : Fin 8, SmallParityFourFrattiniModel i := by
  intro i
  apply smallParityFourFrattiniModel_of_certificates i
  · exact smallParityFourMap_mul i
  · exact smallParityFourMap_eq_one_iff_mem_frattini i
  · intro v
    by_cases hi : i.val < 4
    · exact smallParityFourCoordinateProfile_first i hi
        (fun x => smallParityFour_mem_iff_carrier i x) v
    · exact smallParityFourCoordinateProfile_last i (by omega)
        (fun x => smallParityFour_mem_iff_carrier i x) v

end ReeTwo.SylowModel
