module

public import Theory.Representation.Triality.RestrictedWeights.ConcreteInvolutionDisplacement
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.Twist

/-!
# Coefficient Frobenius under the actual native triality inclusion

Signed Geck root generation extends the literal root equations of a
Geck-to-Spin homomorphism to compatibility with every prime coefficient
Frobenius. The root parameters agree because a field homomorphism preserves
powers.

Specializing to the proved finite Geck-to-Spin comparison and passing through
the original elementary central quotient gives the coefficient action on
`nativePointHom`. The proof uses `toCarrier` and its actual coefficient-action
compatibility throughout. The regular Frobenius and its one-step composition
power are the same maps used by the finite tensor construction. No extra
Frobenius-intertwining premise or alternative carrier is introduced.

Source: GLS3, 2.5.12--13 and 2.8, and Guralnick--Malle,
Classification of 2F-modules II, Section 3.5 and Lemma 8.6.
-/

public section
noncomputable section

namespace Triality.BinaryDegree.CarrierTransport
open Triality.Standard Triality.Standard.OuterOdd Triality.Standard.EvenField
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.SimpleGeckGroup

private theorem geck_word_induction (P : Parameters) {p : SplitGroup P → Prop}
    (hp : ∀ i t, p (positive (typeDRootPairing_baseEquiv 2 i) t))
    (hn : ∀ i t, p (negative (typeDRootPairing_baseEquiv 2 i) t))
    (h1 : p 1) (hm : ∀ g h, p g → p h → p (g * h))
    (hi : ∀ g, p g → p g⁻¹) (g : SplitGroup P) : p g := by
  rcases g with ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨⟨s, j⟩, t, rfl⟩ := hx
      obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
      cases s
      · exact hn i t
      · exact hp i t
  | one => exact h1
  | mul x y hx hy ihx ihy => exact hm ⟨x, hx⟩ ⟨y, hy⟩ ihx ihy
  | inv x hx ih => exact hi ⟨x, hx⟩ ih

variable {k : Type*} [Field k] [IsAlgClosed k] [CharP k 2]

/-- The actual signed-root equations force compatibility with coefficient Frobenius. -/
theorem HasRootFormula.coefficientFrobenius_intertwines {n : ℕ} {hn : 0 < n}
    {f : ExtensionField (binaryParameters n hn) →+* k}
    {e : SplitGroup (binaryParameters n hn) →* Points k}
    (he : HasRootFormula f e) (r : ℕ) (g : SplitGroup (binaryParameters n hn)) :
    e (coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn r) g) =
      frobeniusPointAut k r (e g) := by
  apply geck_word_induction (binaryParameters n hn)
    (p := fun g => e (coefficientSplit (binaryParameters n hn)
      (coefficientFrobenius n hn r) g) = frobeniusPointAut k r (e g))
  · intro i t
    simp only [coefficientSplit_positive, coefficientFrobenius_apply, he.1,
      GraphField.frobenius_positiveSimple, map_pow]
  · intro i t
    simp only [coefficientSplit_negative, coefficientFrobenius_apply, he.2,
      GraphField.frobenius_negativeSimple, map_pow]
  · simp only [map_one]
  · intro g h hg hh
    simp only [map_mul, hg, hh]
  · intro g hg
    simp only [map_inv, hg]

end Triality.BinaryDegree.CarrierTransport

namespace Triality.OuterDisplacement.ConcretePairedTensorSource
open Triality.Standard Triality.Standard.OuterOdd Triality.Standard.EvenField
open Triality.SimplyConnected Triality.BinaryDegree.CarrierTransport
open Triality.RestrictedWeights.Concrete

variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The native central-quotient inclusion intertwines the actual coefficient action. -/
theorem nativePointHom_coefficientFrobenius (n : ℕ) (hn : 0 < n) (r : ℕ)
    (g : BinaryCarrier n hn) :
    nativePointHom k n hn
      (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn r) g) =
        frobeniusPointAut k r (nativePointHom k n hn g) := by
  obtain ⟨x, rfl⟩ := toCarrier_surjective (binaryParameters n hn) g
  calc
    nativePointHom k n hn
        (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn r)
          (toCarrier (binaryParameters n hn) x)) =
      nativePointHom k n hn (toCarrier (binaryParameters n hn)
        (coefficientElementary (binaryParameters n hn) (coefficientFrobenius n hn r) x)) :=
      congrArg (nativePointHom k n hn)
        (coefficientCarrier_toCarrier (binaryParameters n hn) (coefficientFrobenius n hn r) x)
    _ = GeckSpin.finiteComparison k (coefficientEmbedding k n hn)
        (coefficientElementary (binaryParameters n hn) (coefficientFrobenius n hn r) x).val.val :=
      nativePointHom_toCarrier k n hn _
    _ = GeckSpin.finiteComparison k (coefficientEmbedding k n hn)
        (coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn r) x.val.val) :=
      congrArg (GeckSpin.finiteComparison k (coefficientEmbedding k n hn))
        ((congrArg Subtype.val (coefficientElementary_val (binaryParameters n hn)
          (coefficientFrobenius n hn r) x)).trans
          (coefficientFixed_val (binaryParameters n hn) (coefficientFrobenius n hn r) x.val))
    _ = frobeniusPointAut k r (GeckSpin.finiteComparison k (coefficientEmbedding k n hn) x.val.val) :=
      HasRootFormula.coefficientFrobenius_intertwines
        (GeckSpin.finiteComparison_hasRootFormula k (coefficientEmbedding k n hn)) r x.val.val
    _ = frobeniusPointAut k r (nativePointHom k n hn (toCarrier (binaryParameters n hn) x)) :=
      congrArg (frobeniusPointAut k r) (nativePointHom_toCarrier k n hn x).symm

/-- The same action is realized by the original regular Spin Frobenius lift. -/
theorem nativePointHom_regularFrobenius (n : ℕ) (hn : 0 < n) (r : ℕ)
    (g : BinaryCarrier n hn) :
    nativePointHom k n hn
      (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn r) g) =
        (regularFrobeniusLift k r).onPoints (nativePointHom k n hn g) := by
  rw [regularFrobeniusLift_onPoints]
  exact nativePointHom_coefficientFrobenius k n hn r g

/-- The tensor convention uses composition powers of the actual one-step Frobenius. -/
theorem nativePointHom_frobenius_pow (n : ℕ) (hn : 0 < n) (r : ℕ)
    (g : BinaryCarrier n hn) :
    nativePointHom k n hn
      (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn r) g) =
        (GraphField.frobeniusEnd k 1 ^ r)
          (nativePointHom k n hn g) := by
  rw [GraphField.frobenius_onPoints_pow, GraphField.frobeniusEnd_apply]
  exact nativePointHom_coefficientFrobenius k n hn r g


/-- Equality of the literal homomorphism composites used to pull back tensor factors. -/
theorem nativePointHom_comp_coefficientFrobenius (n : ℕ) (hn : 0 < n) (r : ℕ) :
    (nativePointHom k n hn).comp
      (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn r)).toMonoidHom =
    (GraphField.frobeniusEnd k 1 ^ r).comp
      (nativePointHom k n hn) := by
  apply MonoidHom.ext
  exact nativePointHom_frobenius_pow k n hn r

end Triality.OuterDisplacement.ConcretePairedTensorSource
