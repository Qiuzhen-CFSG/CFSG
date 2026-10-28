module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.TensorEstimates
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Inner.Cover
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Inner.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Inner.Coarse
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Inner.Adjoint

/-!
# Assembly of the inner SL₃ fixed-space exclusion

Lift the literal inner operator subgroup through the odd central kernel,
preserving rank and common fixed codimension. A parabolic degree estimate
then forces a non-small repeated word to be the single adjoint endpoint.
Its actual scalar-extension equivalence transfers the independent adjoint
fixed-space estimate back to the original binary representation.

The unconditional `inner_word_estimate` discharges both mathematical estimates:
the root-plane tensor fixed-space bound supplies the degree estimate, and the
strict common-fixed-space obstruction excludes the adjoint endpoint. The
earlier conditional assembly remains available with its original interface.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript
Proposition 4.7 and Lemma 4.5, pp.23–26; Aschbacher–Smith K.3.2, printed
pp.454–456. This module imports the tensor contract directly so that the
source sieve can later import the completed inner argument without a cycle.
-/

public section
noncomputable section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve

open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open ChapterB.QuasisimpleSource
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

set_option backward.isDefEq.respectTransparency false in
/-- The two source estimates imply the published inner-word contract on the
actual normalizer. The first concerns the degree of a non-small word with an
inner offender; the second concerns only the concrete trace-zero adjoint
action. Neither estimate assumes the final word exclusion. -/
theorem inner_word_estimate_of_degree_and_adjoint
    (hk : σ.ker ≤ Subgroup.center _)
    (hdegree : ∀ M : RepeatedModel B σ,
      0 < naturalCount M.block + adjointCount M.block → ¬ M.Small →
      ∀ E : Subgroup SL(3,B.Carrier), IsElementaryTwo E →
        fixedCodim σ E ≤ 2 * rank E → Module.finrank (ZMod 2) V ≤ 8 * B.degree)
    (hadjoint : ∀ ι : B.Carrier →+* SplittingField σ,
      ∀ E : Subgroup SL(3,B.Carrier), IsElementaryTwo E →
        2 * rank E < B.degree * Module.finrank (SplittingField σ)
          (AdjointSpace (SplittingField σ) ⧸
            invariants ((factorRep ι .adjoint).comp E.subtype))) :
    InnerWordEstimate B σ := by
  intro M hp hn A hA _ hi
  obtain ⟨E, hE, _, hr, hc⟩ := Inner.exists_inner_lift B σ hk A hA hi
  by_contra h
  have hsmall : fixedCodim σ E ≤ 2 * rank E := by
    rw [hc, hr]
    exact Nat.le_of_not_gt h
  have hd := hdegree M hp hn E hE hsmall
  obtain ⟨ha, hb, ht⟩ := Inner.single_adjoint_of_non_small B σ M hp hn hd
  obtain ⟨ι, _, hcodim⟩ := Inner.single_adjoint_model B σ M ha hb ht
  have hstrict := hadjoint ι E hE
  rw [← hcodim E] at hstrict
  exact (not_lt_of_ge hsmall) hstrict

/-- Every non-small positive repeated word has fixed codimension strictly
greater than twice the rank of any elementary cubic inner actor. The kernel
may contain the SL₃ center; no degree or fixed-space estimate is assumed. -/
theorem inner_word_estimate (hk : σ.ker ≤ Subgroup.center _) :
    InnerWordEstimate B σ :=
  inner_word_estimate_of_degree_and_adjoint B σ hk
    (Inner.finrank_le_eight_mul_of_inner_actor B σ)
    (Inner.adjoint_fixed_space_estimate B σ)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve
