module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.BaseFour
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.PackedRows

/-!
# The exact finite Schreier-edge obligation

Each candidate is an element of the actual J₂ carrier, by the previously
proved membership of the four-transversal normal forms. Four-point checks
against the fixed step tables suffice for every edge equation. The identity
row is checked here; the full EdgeChecks proposition remains a finite
obligation. No BFS-word equality is needed for this constructor: the edge
equations, generation, and group order establish the coset interpretation.

Source and reproduction: Geometry/source/README.md and
Geometry/source/generate_schreier_data.py. The resulting Schreier certificate
feeds Geometry.SchreierCertificate.rightCosetGeometry.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry
open Sporadic.LeechRelated.J2
open GeneratorPair.SecondOrbitCertificate

/-- Decode a mixed-radix index in the existing certified normal forms. -/
def candidateIndex (x : Point) : Index :=
  let n := lookup 20 normalFormCodes x.val
  (⟨n % 100, Nat.mod_lt _ (by decide)⟩,
    ⟨n / 100 % 63, Nat.mod_lt _ (by decide)⟩,
    ⟨n / 6300 % 24, Nat.mod_lt _ (by decide)⟩,
    ⟨n / 151200 % 4, Nat.mod_lt _ (by decide)⟩)

/-- These candidates already belong to the genuine carrier. -/
def candidate (x : Point) : Carrier :=
  ⟨normalForm (candidateIndex x), ExceptionalParabolics.FirstParabolic.normalForm_mem _⟩

theorem inclusion_candidate (x : Point) :
    inclusion (candidate x) = normalForm (candidateIndex x) := rfl

/-- Retained subgroup powers for each right generator edge. The repeated A
array is correct for letter 2 because the original generator is involutory;
the edge obligation still checks it with the actual letter. -/
def edgePowers (x : Point) (l : Fin 4) : CoefficientTheory.PowerIndex :=
  let n := lookup 5 (![edgePowersA, edgePowersB, edgePowersA, edgePowersBInv] l) x.val
  (⟨n % 5, Nat.mod_lt _ (by decide)⟩, ⟨n / 5 % 5, Nat.mod_lt _ (by decide)⟩)

theorem candidate_zero : candidate 0 = 1 := by
  apply carrier_ext_baseFour
  intro j
  rw [inclusion_candidate, map_one]
  have h : ∀ j : Fin 4, normalForm (candidateIndex 0) (basePoint j) = basePoint j := by
    decide +kernel
  exact h j

/-- Pure finite checks on the exact fixed rows, letters, powers and targets.
The only points checked are the certified base 0, 1, 2, 3. -/
def EdgeChecks : Prop :=
  ∀ x l j, normalForm (candidateIndex x) (tableLetter l (basePoint j)) =
    (leftTable ^ (edgePowers x l).1.val * rightTable ^ (edgePowers x l).2.val)
      (normalForm (candidateIndex (step l x)) (basePoint j))

/-- Actual application of the four-point criterion, producing the precise
Schreier input consumed by the coset-geometry construction. -/
def schreierCertificate_of_edgeChecks (h : EdgeChecks) : SchreierCertificate :=
  schreierCertificate_of_baseFour candidate candidate_zero edgePowers <| by
    simpa only [inclusion_candidate, EdgeChecks] using h

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry

