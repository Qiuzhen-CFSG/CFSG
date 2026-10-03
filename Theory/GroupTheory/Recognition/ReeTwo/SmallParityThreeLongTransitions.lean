module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeLongCoordinates

/-!
# Generator transitions for the long rank-three parity carriers

The collected values of the original root words give a finite certificate for
right multiplication: each generator preserves the proposed carrier and adds
its quotient coordinates. This is checked on the 896 parameter tuples and nine
generators, rather than on arbitrary pairs of carrier elements.

Source: Shinoda (1975), (2.3), pp. 81–82, through `SmallParityThreeGenerators`
and the verified polynomial operations in `CollectedOperations`.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallParityLong
set_option maxRecDepth 32768

private def generator (c : Fin 3) (j : Fin 9) : SylowModel :=
  (![![⟨⟨1,0,0,0,0,0,0,0,0,0⟩, Multiplicative.ofAdd 3⟩,
⟨⟨1,0,0,1,1,1,1,0,0,1⟩, Multiplicative.ofAdd 3⟩,
⟨⟨0,1,0,1,1,0,1,1,1,0⟩, Multiplicative.ofAdd 2⟩,
⟨⟨0,0,0,0,1,0,1,1,0,0⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,1,1,0,1,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,1,1,0,0⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,1,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,1,0⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩],
![⟨⟨1,0,0,0,0,0,0,0,0,0⟩, Multiplicative.ofAdd 3⟩,
⟨⟨1,0,0,1,0,1,0,0,1,1⟩, Multiplicative.ofAdd 3⟩,
⟨⟨0,1,0,1,1,0,1,1,1,0⟩, Multiplicative.ofAdd 2⟩,
⟨⟨0,0,0,0,0,0,1,0,0,0⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,1,1,0,1,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,1,1,0⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,1,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩],
![⟨⟨1,0,0,0,0,0,0,0,0,0⟩, Multiplicative.ofAdd 3⟩,
⟨⟨1,0,0,1,0,1,1,1,1,0⟩, Multiplicative.ofAdd 3⟩,
⟨⟨0,1,0,1,1,0,1,1,1,0⟩, Multiplicative.ofAdd 2⟩,
⟨⟨0,0,0,0,0,0,0,1,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,1,1,0,1,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,1,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩,
⟨⟨0,0,0,0,0,0,0,0,0,1⟩, Multiplicative.ofAdd 0⟩]] : Fin 3 → Fin 9 → SylowModel) c j

set_option maxHeartbeats 8000000 in
private theorem generator_eq : ∀ (c : Fin 3) (j : Fin 9),
    generator c j = smallParityThreeGenerator (index c) j := by decide +kernel


set_option maxHeartbeats 8000000 in
private theorem generator_transition : ∀ (c : Fin 3) (p : Parameters c) (j : Fin 9),
    carrier c (collectedMul (element c p) (generator c j)) ∧
    coordinates c (collectedMul (element c p) (generator c j)) =
      coordinates c (element c p) * coordinates c (generator c j) := by decide +kernel

/-- Right multiplication by each original generator preserves the carrier and
adds its prescribed quotient coordinates. -/
theorem carrier_coordinates_generator (c : Fin 3) (p : Parameters c) (j : Fin 9) :
    carrier c (element c p * smallParityThreeGenerator (index c) j) ∧
    coordinates c (element c p * smallParityThreeGenerator (index c) j) =
      coordinates c (element c p) * coordinates c (smallParityThreeGenerator (index c) j) := by
  rw [← generator_eq, ← collectedMul_eq]
  exact generator_transition c p j

end ReeTwo.SylowModel.SmallParityLong
