module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.G2Recognition.OddCharacteristic.Inputs
public import Theory.Representation.BinaryOffender.PerfectNormalizer
public import Theory.Representation.BinaryOffender.ConjugateDisplacement
public import Theory.Representation.EndFieldDegree

/-!
# Assembly of odd-field G₂ exclusion from model bounds

Faithful conjugation and perfect central descent bound the two-rank of the
literal full binary normalizer by that of Aut(G₂(F)). An offender therefore
gives a normalizer involution with fixed codimension at most four. For fields
larger than three, Schur-field descent gives degree at least 33, while eight
conjugates give degree at most 32. For the ternary field the separate
displacement bound covers the fourteen-dimensional module and outer involutions.

The source is Aschbacher–Smith B.1.13, printed pp.73–74, and the relevant
cross-characteristic argument is Guralnick–Malle, Classification of
2F-modules I, (2.6) and Proposition 4.6, manuscript pp.4 and 14–15.

This module proves the reductions and conditional assembly only. The four
model bounds in `Inputs` remain explicit and must be discharged before this
is the odd-characteristic exclusion. No generalized-Fitting identification
or absolute irreducibility of the original binary action is assumed.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.G2Odd
universe u v w
variable {R : Type u} [Group R] [Finite R] [IsQuasisimple R]
  {F : Type v} [Field F] [Finite F]
  {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Apply the absolute degree input to the actual Schur-field representation;
the specified central quotient and arbitrary covering group are retained. -/
theorem binary_degree_ge (hdegree : LargeFieldDegreeBound.{u,v,w})
    (hq : 3 < Nat.card F) (hchar : ringChar F ≠ 2)
    (e : R ⧸ center R ≃* Atlas.G2.Model F) (hc : pCore 2 R = ⊥)
    (σ : Representation (ZMod 2) R W) (hf : Function.Injective σ)
    (hi : σ.IsIrreducible) : 33 ≤ Module.finrank (ZMod 2) W :=
  Representation.binary_finrank_ge_of_absolute_bound σ hf hi 33
    (hdegree R F hq hchar e hc)

/-- Apply the group generation input inside the unchanged full binary normalizer. -/
theorem degree_le_eight_mul_displacement (hgen : LargeFieldConjugateBound.{u,v,w})
    (hq : 3 < Nat.card F) (hchar : ringChar F ≠ 2)
    (e : R ⧸ center R ≃* Atlas.G2.Model F) (hc : pCore 2 R = ⊥)
    (σ : Representation (ZMod 2) R W) (hf : Function.Injective σ)
    (hi : σ.IsIrreducible) (t : linearNormalizer σ) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    Module.finrank (ZMod 2) W ≤ 8 * fixedCodim (normalizerRepresentation σ) (zpowers t) := by
  let : IsSimpleGroup (R ⧸ center R) := IsQuasisimple.simple
  let : Nontrivial R := (QuotientGroup.mk'_surjective (center R)).nontrivial
  obtain ⟨g, hg⟩ := hgen R F hq hchar e hc W σ hf hi t ht ht2
  exact finrank_le_mul_fixedCodim_of_conjugate_generation (normalizerRepresentation σ)
    ((actionImage σ).subgroupOf (linearNormalizer σ))
    (PerfectNormalizer.fixedSpace_image_eq_bot σ hf hi) t g hg

/-- The independent degree and generation inputs imply the needed displacement gap. -/
theorem large_field_displacement_gt_four
    (hdegree : LargeFieldDegreeBound.{u,v,w}) (hgen : LargeFieldConjugateBound.{u,v,w})
    (hq : 3 < Nat.card F) (hchar : ringChar F ≠ 2)
    (e : R ⧸ center R ≃* Atlas.G2.Model F) (hc : pCore 2 R = ⊥)
    (σ : Representation (ZMod 2) R W) (hf : Function.Injective σ)
    (hi : σ.IsIrreducible) (t : linearNormalizer σ) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    4 < fixedCodim (normalizerRepresentation σ) (zpowers t) := by
  have hlow := binary_degree_ge hdegree hq hchar e hc σ hf hi
  have hupp := degree_le_eight_mul_displacement hgen hq hchar e hc σ hf hi t ht ht2
  omega

/-- Conditional assembly with every independent model premise visible.
This is not yet an unconditional instance of B.1.13. -/
theorem not_ff_of_model_bounds
    (hrank : AutomorphismRankBound.{v}) (hdegree : LargeFieldDegreeBound.{u,v,w})
    (hgen : LargeFieldConjugateBound.{u,v,w}) (hthree : TernaryDisplacementBound.{u,v,w})
    (hq : 2 < Nat.card F) (hchar : ringChar F ≠ 2)
    (e : R ⧸ center R ≃* Atlas.G2.Model F) (hc : pCore 2 R = ⊥)
    (σ : Representation (ZMod 2) R W) (hf : Function.Injective σ)
    (hi : σ.IsIrreducible) : ¬ IsFFModule (normalizerRepresentation σ) := by
  intro hff
  obtain ⟨t, ht, ht2, hsmall⟩ := PerfectNormalizer.exists_small_involution σ hf hi e hff
  have hle : fixedCodim (normalizerRepresentation σ) (zpowers t) ≤ 4 :=
    hsmall.trans (hrank F hq hchar)
  by_cases hq3 : Nat.card F = 3
  · exact (Nat.not_lt_of_ge hle) (hthree R F hq3 hchar e hc W σ hf hi t ht ht2)
  · exact (Nat.not_lt_of_ge hle)
      (large_field_displacement_gt_four hdegree hgen (by omega) hchar e hc σ hf hi t ht ht2)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.G2Odd
