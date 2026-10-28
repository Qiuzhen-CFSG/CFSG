module

public import Theory.Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.TensorEstimates

/-!
# The source adjoint premise for the inner SL₃ sieve

Specialize the uniform strict trace-zero adjoint estimate to the specified
binary field and the actual splitting field of the representation. The
coefficient embedding is arbitrary, so this includes the Frobenius-twisted
embedding constructed by `Inner.single_adjoint_model`. This is exactly the
`hadjoint` premise of `inner_word_estimate_of_degree_and_adjoint`; the
independent parabolic degree estimate remains with that theorem's owner.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript
Lemma 4.5, pp.23–24, paragraph 2; Aschbacher–Smith K.3.2, pp.454–456.
-/

public section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open ChapterB.QuasisimpleSource
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- The literal adjoint fixed-space premise of the inner-word assembly. -/
theorem adjoint_fixed_space_estimate (ι : B.Carrier →+* SplittingField σ)
    (E : Subgroup SL(3,B.Carrier)) (hE : IsElementaryTwo E) :
    2 * rank E < B.degree * Module.finrank (SplittingField σ)
      (AdjointSpace (SplittingField σ) ⧸
        invariants ((factorRep ι .adjoint).comp E.subtype)) :=
  AdjointFixedSpaces.strict_common_fixedCodim B.degree_pos B.card_eq ι E hE

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner
