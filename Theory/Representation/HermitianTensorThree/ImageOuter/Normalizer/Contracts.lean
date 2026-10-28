module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Actions

/-!
# Two independent inputs to the Hermitian normalizer argument

The scalar-centralizer assertion identifies binary intertwiners of the given
SL₃ action. The induced-action assertion describes the automorphism of that
image induced by a normalizer element, allowing all inner-diagonal matrices
and coefficient automorphisms. Together they imply actual normalizer coverage:
after removing the prescribed action, the remaining intertwiner is a scalar,
which is itself a GL₃ congruence.

These contracts are proved in `Normalizer.Centralizer` and
`Normalizer.InducedAction`, respectively, and discharged in `Normalizer`.
Source: Aschbacher–Smith, combined manuscript of
1 March 2004, H.4.2 setup, printed p.380.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter
variable (n : ℕ) [NeZero n]

/-- The binary linear centralizer of the actual SL₃ image consists of fixed-field scalars. -/
def ScalarCentralizerCoverage : Prop :=
  ∀ e : Space n ≃ₗ[ZMod 2] Space n,
    (∀ a : Cover n, e * binaryActionHom n a = binaryActionHom n a * e) →
      ∃ c : (F n)ˣ, e = fixedScalar n c

/-- Only inner-diagonal and coefficient automorphisms of the image occur in its binary normalizer. -/
def InducedActionCoverage : Prop :=
  ∀ e ∈ binaryNormalizer n,
    ∃ (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (τ : E n ≃+* E n),
      ∀ a : Cover n,
        e * binaryActionHom n a * e⁻¹ =
          semilinearCongruence n g τ * binaryActionHom n a * (semilinearCongruence n g τ)⁻¹

end Representation.HermitianTensorThree.ImageOuter
