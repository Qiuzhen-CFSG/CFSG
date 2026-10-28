module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCoordinatesA256
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutFrattiniA256
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCountsA256

/-!
# Assembly of the order-256 small even Frattini models

The exact candidate parametrizations and their surjective coordinate functions
are proved in `SmallEvenTwoAutCoordinatesA256`. This module assembles the
multiplication, Frattini-kernel, and intrinsic counting certificates in the
basis convention of `SmallEvenAutProfilesA`.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified Ree two root model.
-/

namespace ReeTwo.SylowModel
open ReeTwo.SmallEvenAutProfilesA

set_option maxRecDepth 8192 in
/-- Algebraic and counting certificates for the fixed coordinates realize all eleven models. -/
public theorem smallEvenTwoAutFourModelsA256_of_certificates
    (hmul : ∀ (i : Fin 11) x y, a256Map i (x * y) = a256Map i x * a256Map i y)
    (hker : ∀ (i : Fin 11) x, a256Map i x = 1 ↔
      x ∈ frattini (smallEvenCandidate (a256Index i)))
    (hcounts : ∀ (i : Fin 11) v,
      a256CoordinateProfile i v = fourProfile (a256Row i) v) :
    ∀ j : Fin 16, 5 ≤ j.val → FourModel (smallEvenCandidate (fourIndex j)) j := by
  have models (i : Fin 11) : FourModel (smallEvenCandidate (a256Index i)) (a256Row i) := by
    let π : smallEvenCandidate (a256Index i) →* FourQuotient :=
      MonoidHom.mk' (a256Map i) (hmul i)
    refine ⟨π, a256Map_surjective i, ?_, hcounts i⟩
    ext x
    exact hker i x
  intro j hj
  fin_cases j
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · exact models 0
  · exact models 1
  · exact models 2
  · exact models 3
  · exact models 4
  · exact models 5
  · exact models 6
  · exact models 7
  · exact models 8
  · exact models 9
  · exact models 10

end ReeTwo.SylowModel

namespace ReeTwo.SylowModel
open ReeTwo.SmallEvenAutProfilesA

/-- The fixed coordinates realize every small even rank-four Frattini model. -/
public theorem smallEvenTwoAutFourModelsA256 :
    ∀ j : Fin 16, 5 ≤ j.val →
      FourModel (smallEvenCandidate (fourIndex j)) j := by
  exact smallEvenTwoAutFourModelsA256_of_certificates
    a256Map_mul a256Map_eq_one_iff_frattini a256CoordinateProfile_eq

end ReeTwo.SylowModel
