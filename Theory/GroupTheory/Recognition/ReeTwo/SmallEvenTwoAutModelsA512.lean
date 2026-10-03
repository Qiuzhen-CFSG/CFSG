module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenAutCoordinatesA512
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenAutCountsA512
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenAutFrattiniA512

/-!
# Assembly of the six order-512 small even Frattini models

The coordinate sections realize every quotient label on the original candidate
subgroups. Multiplicativity and identification of the identity fiber with
Frattini turn these coordinates into surjective quotient homomorphisms. The
counting certificates use the same functions and the precise intrinsic tests in
`SmallEvenAutProfilesA`. This module assembles the proved certificates into
unconditional models for candidates 0, 1, 2, 4, 5 and 6.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified root model;
see `SmallEvenAutCoordinatesA512` for the basis and coordinate conventions.
-/

namespace ReeTwo.SylowModel
open ReeTwo.SmallEvenAutProfilesA

/-- Assemble the five rank-four models from algebraic and counting certificates. -/
public theorem smallEvenTwoAutFourModelsA512_of_certificates
    (hmul : ∀ (j : Fin 5) x y, smallEvenFourMapA512 j (x * y) =
      smallEvenFourMapA512 j x * smallEvenFourMapA512 j y)
    (hker : ∀ (j : Fin 5) x, smallEvenFourMapA512 j x = 1 ↔
      x ∈ frattini (smallEvenCandidate (fourIndex (smallEvenFourRowA512 j))))
    (hcounts : ∀ (j : Fin 5) v, smallEvenFourCoordinateProfileA512 j v =
      fourProfile (smallEvenFourRowA512 j) v) :
    ∀ j : Fin 16, j.val < 5 → FourModel (smallEvenCandidate (fourIndex j)) j := by
  intro j hj
  let k : Fin 5 := ⟨j.val, hj⟩
  have hk : smallEvenFourRowA512 k = j := Fin.ext rfl
  rw [← hk]
  let π : smallEvenCandidate (fourIndex (smallEvenFourRowA512 k)) →* FourQuotient :=
    MonoidHom.mk' (smallEvenFourMapA512 k) (hmul k)
  refine ⟨π, smallEvenFourMapA512_surjective k, ?_, ?_⟩
  · ext x
    exact hker k x
  · exact hcounts k

/-- Assemble candidate 4's rank-three model from algebraic and counting certificates. -/
public theorem smallEvenTwoAutThreeModelA512_of_certificates
    (hmul : ∀ x y, smallEvenThreeMapA512 (x * y) =
      smallEvenThreeMapA512 x * smallEvenThreeMapA512 y)
    (hker : ∀ x, smallEvenThreeMapA512 x = 1 ↔ x ∈ frattini (smallEvenCandidate 4))
    (hcounts : ∀ v, smallEvenThreeCoordinateProfileA512 v = threeProfile v) :
    ThreeModel (smallEvenCandidate 4) := by
  let π : smallEvenCandidate 4 →* ThreeQuotient := MonoidHom.mk' smallEvenThreeMapA512 hmul
  refine ⟨π, smallEvenThreeMapA512_surjective, ?_, ?_⟩
  · ext x
    exact hker x
  · exact hcounts

/-- The five order-512 rank-four candidates realize their prescribed Frattini profiles. -/
public theorem smallEvenTwoAutFourModelsA512 :
    ∀ j : Fin 16, j.val < 5 → FourModel (smallEvenCandidate (fourIndex j)) j :=
  smallEvenTwoAutFourModelsA512_of_certificates
    smallEvenFourMapA512_mul
    smallEvenFourMapA512_eq_one_iff_mem_frattini
    smallEvenFourCoordinateProfileA512_eq

/-- Candidate 4 realizes the prescribed rank-three Frattini profile. -/
public theorem smallEvenTwoAutThreeModelA512 : ThreeModel (smallEvenCandidate 4) :=
  smallEvenTwoAutThreeModelA512_of_certificates
    smallEvenThreeMapA512_mul
    smallEvenThreeMapA512_eq_one_iff_mem_frattini
    smallEvenThreeCoordinateProfileA512_eq

end ReeTwo.SylowModel
