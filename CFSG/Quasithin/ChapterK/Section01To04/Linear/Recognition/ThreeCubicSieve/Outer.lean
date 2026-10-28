module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.TensorEstimates
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Schur
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Remaining
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors

/-!
# Outer-actor exclusion for the SL₃ cubic sieve

Every non-small repeated word excludes an elementary cubic outer actor of
rank at most twice the defining-field degree. The scalar-moving calculation,
including its strict degree-8r endpoint, reduces to Schur-linear actors.
The single-adjoint and other tensor-word estimates then cover every remaining
word. Their actual operator constructions require only the central kernel of
the SL₃ representation, with no faithfulness assumption on that cover.

The source application supplies this kernel condition from the literal
inflated action. The independent inner estimate and the source actor-rank
bound remain with the cubic sieve's assembly owner.

Source: Aschbacher–Smith K.3.2, printed pp.454–456; Guralnick–Malle,
Classification of 2F-modules II, Proposition 4.8, manuscript pp.26–28.
-/

public section
noncomputable section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve

open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open ChapterB.QuasisimpleSource
open scoped MatrixGroups

section Normalizer

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- The proved scalar-moving reduction discharges that entire branch;
only the two explicitly stated Schur-linear estimates remain. -/
theorem outer_word_estimate_of_schurLinear_branches
    (hadjoint : Outer.SchurLinearAdjointEstimate B σ)
    (htensor : Outer.SchurLinearTensorEstimate B σ) : OuterWordEstimate B σ := by
  intro M hp hn A hA hc hr ho
  by_contra hd
  have hd' := Nat.le_of_not_gt hd
  have hs := Outer.schurLinear_of_small_actor B σ M hp hn A hA hr hd'
  by_cases ha : Outer.SingleAdjoint B σ M
  · exact hd (hadjoint M ha A hA hc hr ho hs)
  · exact hd (htensor M hp hn ha A hA hc hr ho hs)

/-- All outer types satisfy the strict common-fixed-space estimate on every
non-small repeated word. The representation may have a central SL₃ kernel. -/
theorem outer_word_estimate (hk : σ.ker ≤ Subgroup.center _) :
    OuterWordEstimate B σ :=
  outer_word_estimate_of_schurLinear_branches B σ
    (Outer.adjoint_estimate B σ hk) (Outer.tensor_estimate B σ hk)

/-- Application to the literal model and cubic actor used by the source
sieve. The independent inner estimate remains with its existing owner. -/
theorem small_of_inner_and_schurLinear_estimates
    (hinner : InnerWordEstimate B σ)
    (hadjoint : Outer.SchurLinearAdjointEstimate B σ)
    (htensor : Outer.SchurLinearTensorEstimate B σ)
    (hact : ∃ g, σ g ≠ 1) (M : RepeatedModel B σ)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hc : IsCubic (normalizerRepresentation σ) A) (hr : rank A ≤ 2 * B.degree)
    (hd : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A) : M.Small :=
  small_of_actor_estimates B σ hinner
    (outer_word_estimate_of_schurLinear_branches B σ hadjoint htensor)
    hact M A hA hc hr hd

/-- The proved outer estimate leaves only the independent inner calculation
in the literal repeated-word sieve. -/
theorem small_of_inner_estimate (hk : σ.ker ≤ Subgroup.center _)
    (hinner : InnerWordEstimate B σ)
    (hact : ∃ g, σ g ≠ 1) (M : RepeatedModel B σ)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hc : IsCubic (normalizerRepresentation σ) A) (hr : rank A ≤ 2 * B.degree)
    (hd : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A) : M.Small :=
  small_of_actor_estimates B σ hinner (outer_word_estimate B σ hk)
    hact M A hA hc hr hd

end Normalizer

section Source

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {B : BinaryField}

/-- Discharge the outer-estimate premise of `finrank_lt_eight_mul_of_estimates`
and `absolute_models_of_estimates` on the original source action. Faithfulness
is used on the ambient action, so inflation along a central cover is allowed. -/
theorem inflated_outer_word_estimate {K : GroupClass}
    (h : SourceHypothesis K ρ L) (C : LinearCover B 3 L) :
    let := h.finite_module
    let := inflated_irreducible ρ C h.irreducible
    OuterWordEstimate B (inflated ρ C) := by
  let := h.finite_module
  let := inflated_irreducible ρ C h.irreducible
  exact outer_word_estimate B (inflated ρ C) (inflated_central_kernel ρ C h.faithful)

end Source

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve
