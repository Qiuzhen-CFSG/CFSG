module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit.Coordinates
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Coordinates
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Algebraic words for the rational nonsplit triality torus

The scalar group has orders q³+1 and q+1 on its two factors. Its four
simple-coroot parameters are (a,b,a⁻ᑫ,aᑫ²). The normalizer words are the
central simple reflection, the square of the folded Coxeter word, and
its cube. All are points of the genuine Clifford Spin group.

`RationalRealization` asks for their simultaneous descent, through one
conjugator, into the original graph-field carrier. `WeylLaws` asks for
calculations in the algebraic group and is independent of that descent.
Neither assertion is supplied by this module. Their producers and the
three-primary assembly are distinct proof obligations.

Source: GLS3 §§2.1–2.4 (rational tori and fixed points), and the calculation
underlying Theorem 6.1.4, `refs/KGroup/GLS3/chapter6.tex`.
-/

@[expose] public section
noncomputable section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
open Subgroup
open Triality.SimplyConnected
open Triality.SimplyConnected.Pinning

abbrev Ambient := Points Scalars

def rawTorus (n : ℕ) : Coordinates n →* Ambient :=
  (CorootTorus.pointHom Scalars).comp (expandHom n)

theorem rawTorus_injective (n : ℕ) : Function.Injective (rawTorus n) :=
  (CorootTorus.parameter_injective Scalars).comp (expand_injective n)

/-- Product on the three mutually orthogonal outer nodes, followed by the central node. -/
def coxeter : Ambient :=
  simpleNormalizer Scalars 0 * simpleNormalizer Scalars 2 *
    simpleNormalizer Scalars 3 * simpleNormalizer Scalars 1

def reflectionWord : Ambient := simpleNormalizer Scalars 1
def cycleWord : Ambient := coxeter ^ 2
def inverterWord : Ambient := coxeter ^ 3

/-- Algebraic Weyl calculations, before rational descent. -/
structure WeylLaws (n : ℕ) : Prop where
  reflection_action : ∀ a, reflectionWord * rawTorus n a * reflectionWord⁻¹ =
    rawTorus n (reflection n a)
  cycle_order : orderOf cycleWord = 3
  cycle_outside : cycleWord ∉ (rawTorus n).range
  cycle_normalizes : cycleWord ∈ normalizer ((rawTorus n).range : Set Ambient)
  inverter_action : ∀ a, inverterWord * rawTorus n a * inverterWord⁻¹ =
    (rawTorus n a)⁻¹

/-- The same conjugator descends the torus and all required Weyl words.
This is a concrete comparison with Spin points, not a covering-group premise. -/
structure RationalRealization (n : ℕ) (hn : 0 < n) where
  embedding : Standard.BinaryCarrier n hn →* Ambient
  embedding_injective : Function.Injective embedding
  conjugator : Ambient
  torus : Coordinates n →* Standard.BinaryCarrier n hn
  torus_eq : ∀ a, embedding (torus a) = conjugator⁻¹ * rawTorus n a * conjugator
  reflection : Standard.BinaryCarrier n hn
  cycle : Standard.BinaryCarrier n hn
  inverter : Standard.BinaryCarrier n hn
  reflection_eq : embedding reflection = conjugator⁻¹ * reflectionWord * conjugator
  cycle_eq : embedding cycle = conjugator⁻¹ * cycleWord * conjugator
  inverter_eq : embedding inverter = conjugator⁻¹ * inverterWord * conjugator

end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
