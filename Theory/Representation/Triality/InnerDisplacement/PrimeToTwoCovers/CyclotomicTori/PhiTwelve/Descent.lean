module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve.SpinTorus
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve.Lang
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent

/-!
# Descent of the cyclic torus to the literal triality carrier

Lang surjectivity supplies a conjugator c with F(c) = c (n₁ n₀)⁻¹.
Conjugating the torus in `SpinTorus` by c therefore places it in the ordinary
graph-field fixed group. The proved Geck–Spin fixed-point comparison and
`ConcreteBruhat.FixedDescent.carrierFixedEquiv` then place it injectively in
`Standard.BinaryCarrier`, with order exactly q⁴−q²+1.

Both comparisons retain the original elementary subgroup and its central
quotient. Source: GLS3 §§2.1–2.2; Steinberg, §10.1
(`refs/KGroup/GLS3/Chapter2St2.tex`).
-/

@[expose] public section

noncomputable section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve
open Triality.SimplyConnected
variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

/-- A conjugator solving the exact Lang equation for the chosen two-reflection word. -/
def langWitness (n : ℕ) (hn : 0 < n) : Points k :=
  (graphField_lang_surjective k n hn ((normalizerWord k)⁻¹)).choose⁻¹

theorem graphField_langWitness (n : ℕ) (hn : 0 < n) :
    GraphField.sigma k n (langWitness k n hn) = langWitness k n hn * (normalizerWord k)⁻¹ := by
  let x := (graphField_lang_surjective k n hn ((normalizerWord k)⁻¹)).choose
  have h : x * (GraphField.sigma k n x)⁻¹ = (normalizerWord k)⁻¹ :=
    (graphField_lang_surjective k n hn ((normalizerWord k)⁻¹)).choose_spec
  change GraphField.sigma k n x⁻¹ = x⁻¹ * (normalizerWord k)⁻¹
  rw [map_inv]
  simpa only [inv_mul_cancel_left] using congrArg (fun y => x⁻¹ * y) h

private theorem conjugate_fixed (n : ℕ) (hn : 0 < n) (z : Parameters k n) :
    langWitness k n hn * spinEmbedding k n z * (langWitness k n hn)⁻¹ ∈
      GraphField.fixedSubgroup k n := by
  have ht : GraphField.sigma k n (spinEmbedding k n z) =
      normalizerWord k * spinEmbedding k n z * (normalizerWord k)⁻¹ := by
    calc
      _ = normalizerWord k * ((normalizerWord k)⁻¹ *
        GraphField.sigma k n (spinEmbedding k n z) * normalizerWord k) *
          (normalizerWord k)⁻¹ := by group
      _ = _ := by rw [spinEmbedding_twisted]
  change GraphField.sigma k n
    (langWitness k n hn * spinEmbedding k n z * (langWitness k n hn)⁻¹) =
      langWitness k n hn * spinEmbedding k n z * (langWitness k n hn)⁻¹
  rw [map_mul, map_mul, map_inv, graphField_langWitness, ht]
  group

/-- The torus now lies in the ordinary graph-field fixed group. -/
def fixedEmbedding (n : ℕ) (hn : 0 < n) : Parameters k n →* GraphField.FixedGroup k n :=
  (((MulAut.conj (langWitness k n hn)).toMonoidHom).comp (spinEmbedding k n)).codRestrict
    (GraphField.fixedSubgroup k n) (by exact conjugate_fixed k n hn)

theorem fixedEmbedding_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (fixedEmbedding k n hn) := by
  intro x y h
  exact spinEmbedding_injective k n
    ((MulAut.conj (langWitness k n hn)).injective (congrArg Subtype.val h))

/-- The comparison retains the literal elementary subgroup and central quotient. -/
def carrierFixedEquiv (n : ℕ) (hn : 0 < n) :
    Standard.BinaryCarrier n hn ≃* GraphField.FixedGroup k n :=
  (Standard.ConcreteBruhat.FixedDescent.carrierFixedEquiv (Standard.binaryParameters n hn) rfl).trans
    (Standard.binarySpinFixedEquiv k n hn)

/-- The constructed twelfth-cyclotomic torus inside the original finite carrier. -/
def embedding (n : ℕ) (hn : 0 < n) : Parameters k n →* Standard.BinaryCarrier n hn :=
  (carrierFixedEquiv k n hn).symm.toMonoidHom.comp (fixedEmbedding k n hn)

theorem embedding_injective (n : ℕ) (hn : 0 < n) : Function.Injective (embedding k n hn) :=
  (carrierFixedEquiv k n hn).symm.injective.comp (fixedEmbedding_injective k n hn)

theorem card_range (n : ℕ) (hn : 0 < n) :
    Nat.card (embedding k n hn).range = order (2 ^ n) :=
  (Nat.card_congr (MonoidHom.ofInjective (embedding_injective k n hn)).symm.toEquiv).trans
    (card_parameters k n hn)

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve
