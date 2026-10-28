module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.ReeF4.ElementaryTwoBound
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.SourceBinary

/-!
# Applying the finite Ree tensor theorem to the original B.4.2 action

The original layer is normal and quasisimple, and its irreducible restriction
makes the ambient action irreducible. Actual outer-element containment and the
proved elementary order bound give rank at most five times the field exponent.
The new source tensor/cover estimate gives fixed codimension at least ten times
that exponent, contradicting the original FF offender.

The three universal finite Steinberg clauses remain explicit in this source
consumer. Their producers must prove restricted irreducibility, parameter
distinction and tensor realization; this file does not assume a desired local
fixed-space estimate or an FF-exclusion certificate.
Source: Aschbacher–Smith B.4.2; Guralnick–Malle II, Lemma 8.8.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.AlgebraicGroup ReeF4.BinaryDegree.ExceptionalTensor
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem ambient_irreducible (h : ChapterK.RankOne.SourceHypotheses ρ L) :
    Representation.IsIrreducible ρ := by
  let := h.irreducible
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp L.subtype)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (ρ.comp L.subtype) :=
    ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule g.val hv⟩
  rcases eq_bot_or_eq_top T with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (ρ.comp L.subtype) => U.toSubmodule) hb
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (ρ.comp L.subtype) => U.toSubmodule) ht

/-- Literal B.4.2 Ree exclusion once the full finite exceptional tensor
classification clauses are supplied by their independent source producer. -/
theorem reeF4_excluded_of_finite_tensor_classification
    (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    {m : ℕ} (hm : 0 < m) (e : L ⧸ center L ≃* _root_.ReeF4.Model m)
    (hirr : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2]
      (B : ZMod (2 * m + 1) → AlgebraicFactor F),
      (∀ i, (B i).IsExceptionalBasic) → Representation.IsIrreducible
        (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ)
    (hunique : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2]
      (B C : ZMod (2 * m + 1) → AlgebraicFactor F),
      (∀ i, (B i).IsExceptionalBasic) → (∀ i, (C i).IsExceptionalBasic) →
      Nonempty (Equiv
        (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ
        (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) C).ρ) →
      ∀ i, AreEquivalentRepresentations (B i).action (C i).action)
    (hreal : ∀ (F W : Type v) [Field F] [IsAlgClosed F] [CharP F 2]
      [AddCommGroup W] [Module F W] [FiniteDimensional F W]
      (σ : Representation F (_root_.ReeF4.Model m) W), Representation.IsIrreducible σ →
      ∃ B : ZMod (2 * m + 1) → AlgebraicFactor F,
        (∀ i, (B i).IsExceptionalBasic) ∧ Nonempty (Equiv σ
          (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ)) : False := by
  let : L.Normal := h.layer_normal
  let := h.quasisimple
  let := h.irreducible
  let : Representation.IsIrreducible ρ := ambient_irreducible h
  have hb := _root_.ReeF4.FixedSpaceEstimate.binaryModelInvolutionBound_of_finite_tensor_classification
    hm hirr hunique hreal
  have hc := _root_.ReeF4.FixedSpaceEstimate.coverInvolutionBound_of_binary_source.{u,v} hm hb
  have hg := ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.ReeF4.absoluteGap_of_involution_bound
    L hm h.fitting e (_root_.ReeF4.ElementaryTwoBound.card_le m hm) hc
  exact ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.not_ff_of_absoluteGap
    L ρ h.faithful hg hff

end CFSG.Quasithin.ChapterB.SourceClassification
