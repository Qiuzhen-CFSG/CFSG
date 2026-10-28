module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticSpace.Coordinates

/-!
# Source coordinate formulas for the Leech generators

Lemma 23.10(4) specifies a Golay sign change and a coordinate permutation on
the twisted code–cocode space. The permutation descends from the actual binary
coordinate permutation, so its inverse-coordinate convention is fixed. The
sign formula retains both the parity-dependent intersection and half-overlap
corrections. These definitions do not assert equivariance; the lattice and
triality calculations must each prove that they induce these same formulas.

Source: Aschbacher, *Sporadic Groups*, Lemma 23.10(4), printed p. 120,
and the generator comparison following Lemma 27.5, printed p. 148.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- The actual Golay coordinate permutation descended to the cocode. -/
def sourceCocodePermutation (σ : Mathieu24CodeModel) : Cocode →ₗ[Bit] Cocode :=
  golay.mapQ golay (coordinatePermutation σ.val).toLinearMap
    (fun J hJ => (σ.prop J).mp hJ)

@[simp] theorem sourceCocodePermutation_mk (σ : Mathieu24CodeModel) (J : BinaryWord) :
    sourceCocodePermutation σ (Submodule.Quotient.mk J) =
      Submodule.Quotient.mk (coordinatePermutation σ.val J) := rfl

/-- The source `β` coordinate formula, with `w'(i) = w(σ⁻¹ i)`. -/
def sourcePermutationCoordinates (σ : Mathieu24CodeModel)
    (x : QuadraticCoordinates) : QuadraticCoordinates :=
  ⟨parkerCodeEquiv σ x.code, sourceCocodePermutation σ x.cocode⟩

/-- The source `ε_Y` formula. The additions here are inside the code and cocode;
the outer space still has its separately specified twisted addition. -/
def sourceSignCoordinates (Y : golay) (x : QuadraticCoordinates) : QuadraticCoordinates :=
  ⟨x.code + cocodeParity x.cocode • Y +
      ((1 + cocodeParity x.cocode) * golayHalfOverlap x.code Y +
        cocodePairing Y x.cocode) • golayOne,
    x.cocode + (1 + cocodeParity x.cocode) • intersectionCocode x.code Y⟩

@[simp] theorem sourceSignCoordinates_zero (Y : golay) :
    sourceSignCoordinates Y 0 = 0 := by
  apply QuadraticCoordinates.ext <;>
    simp [sourceSignCoordinates, quadraticCoordinates_zero_eq, coordinateZero]

@[simp] theorem sourcePermutationCoordinates_zero (σ : Mathieu24CodeModel) :
    sourcePermutationCoordinates σ 0 = 0 := by
  apply QuadraticCoordinates.ext <;>
    simp [sourcePermutationCoordinates, quadraticCoordinates_zero_eq, coordinateZero]

end Sporadic.Monster.Construction.LocalC
