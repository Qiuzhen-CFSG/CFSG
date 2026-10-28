module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Swap
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.PairDisplacement.Intertwiners
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.PairDisplacement.Inner
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.PairDisplacement.NormalizerCases

/-!
# Displacement of normalizing involutions on the concrete natural G₂ pair

Every nonidentity linear involution normalizing the irreducible natural pair
moves at least fifteen dimensions. Faithfulness and inner-field coverage split
the literal induced automorphism into an involutory inner action or an inner
twist of half-degree Frobenius. In the inner case, the natural no-transvection
theorem and tensor rank calculation give displacement at least sixteen. In the
outer case, the actual Frobenius actions exchange the two factors, and Schur
rigidity and the involution equation reduce the operator to a twisted swap.

The final theorem `pair_displacement` discharges both inputs of the retained
conditional assembly. Irreducibility is its only representation-theoretic
premise; it needs no displacement or normal-form hypothesis. It holds at every
twist position, in particular at the source positions `i < s`. Arbitrary-module
recognition and binary descent remain with the separate `HalfTensor` owner.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56; see `G2CubicDegree/Source.md`.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
open Representation.BinaryOffender.NaturalTensor
variable (F K : Type*) [Field F] [Finite F] [CharP F 2]
  [Field K] [Algebra F K] [CharP K 2] [IsAlgClosed K] (i s : ℕ)
  [Representation.IsIrreducible (k := K) (G := Atlas.G2.Model F)
    (V := PairSpace F K) (pairRep F K i s)]

/-- Conditional assembly from the universal inner estimate and the actual
normalizer case split, with all scalar ambiguities discharged. -/
theorem pair_displacement_of_inner_bound_and_cases
    (hinner : ∀ g : Atlas.G2.Model F, g ≠ 1 → g * g = 1 →
      16 ≤ operatorFixedCodim (k := K) (V := PairSpace F K) (pairRep F K i s g))
    (T : Module.End K (PairSpace F K)) (α : MulAut (Atlas.G2.Model F))
    (hne : T ≠ 1) (hT2 : T * T = 1)
    (hT : ∀ h, T * pairRep F K i s h = pairRep F K i s (α h) * T)
    (hcases : (∃ g : Atlas.G2.Model F, g * g = 1 ∧ α = MulAut.conj g) ∨
      ∃ f g : NaturalScalarSpace F K ≃ₗ[K] NaturalScalarSpace F K,
        ∀ h, (pairExchange F K f g).toLinearMap * pairRep F K i s h =
          pairRep F K i s (α h) * (pairExchange F K f g).toLinearMap) :
    15 ≤ operatorFixedCodim (k := K) (V := PairSpace F K) T := by
  rcases hcases with ⟨g, hg, hα⟩ | ⟨f, g, hS⟩
  · have he := pair_inner_intertwiner_eq F K i s T α hT2 hT g hg hα
    have hn : g ≠ 1 := by
      intro h
      apply hne
      simpa [h] using he
    rw [he]
    exact (by decide : 15 ≤ 16).trans (hinner g hn hg)
  · exact pair_exchange_intertwiner_displacement F K i s T α hT2 hT f g hS

/-- Every nonidentity normalizing involution of the irreducible natural pair
over a defining field of degree `2 * s` moves at least fifteen dimensions.
The inner estimate and the actual Frobenius-exchange alternative are proved
internally; no position restriction beyond irreducibility is needed. -/
theorem pair_displacement
    (hs : 0 < s) (hF : Nat.card F = 2 ^ (2 * s))
    (T : Module.End K (PairSpace F K)) (α : MulAut (Atlas.G2.Model F))
    (hne : T ≠ 1) (hT2 : T * T = 1)
    (hT : ∀ h, T * pairRep F K i s h = pairRep F K i s (α h) * T) :
    15 ≤ operatorFixedCodim (k := K) (V := PairSpace F K) T := by
  exact pair_displacement_of_inner_bound_and_cases F K i s
    (pair_inner_displacement F K i s) T α hne hT2 hT
    (pair_normalizer_cases F K i s hs hF T α hT2 hT)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
