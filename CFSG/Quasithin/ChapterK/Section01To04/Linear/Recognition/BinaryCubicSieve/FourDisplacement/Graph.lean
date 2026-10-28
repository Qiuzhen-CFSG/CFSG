module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LocalData
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.Quotient
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Reversing the A₃ diagram without losing actors

Inverse transpose followed by the longest coordinate exchange preserves the
positive roots of binary SL₄ and reverses the three simple roots. Composing a
representation with this actual group automorphism therefore reverses its
local highest-vector support. Its action image is unchanged, so the entire
linear normalizer and its tautological action are unchanged as well. The
common-fixed-space estimate transports with all outer actors retained.

This is the symmetry reduction between the two adjacent-support cases in the
K.3.2 binary sieve. Source: Aschbacher–Smith, printed pp.451,454–455; the GM
manuscript *Classification of 2F-modules, II*, Propositions 4.7–4.8. This module
proves the transport, not either remaining displacement estimate.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

open Representation Representation.BinaryOffender
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

/-- The longest coordinate exchange in binary SL₄. -/
def longestExchange : Group :=
  ⟨!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0], by decide⟩

/-- Inverse transpose followed by coordinate reversal preserves the positive
roots and exchanges the two ends of the A₃ diagram. -/
def diagramReversal : MulAut Group :=
  (BinaryLinear.OuterCyclic.graphSL 4).trans (MulAut.conj longestExchange)

theorem diagramReversal_upper (i j : Fin 4) (hij : i < j) :
    diagramReversal (Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) (1 : ZMod 2)) =
      Matrix.SpecialLinearGroup.transvection
        (ne_of_lt (Fin.rev_lt_rev.mpr hij)) (1 : ZMod 2) := by
  revert i j
  decide

theorem diagramReversal_lower (i : Fin 3) :
    diagramReversal (simpleLower i) = simpleLower i.rev := by
  revert i
  decide

theorem diagramReversal_swap (i : Fin 3) :
    diagramReversal (simpleSwap i) = simpleSwap i.rev := by
  revert i
  decide

attribute [local irreducible] diagramReversal

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

abbrev diagramTwist (σ : Representation (ZMod 2) Group V) :
    Representation (ZMod 2) Group V := σ.comp diagramReversal.toMonoidHom

theorem diagramTwist_apply (σ : Representation (ZMod 2) Group V) (g : Group) :
    diagramTwist σ g = σ (diagramReversal g) := rfl

/-- Twisting preserves the literal highest vector and reverses its support. -/
theorem localHighestVector_diagramTwist
    {σ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector σ J v) :
    LocalHighestVector (diagramTwist σ) (J.image Fin.rev) v := by
  constructor
  · intro i j hij
    rw [diagramTwist_apply, diagramReversal_upper i j hij]
    exact h.upper_fixed _ _ (Fin.rev_lt_rev.mpr hij)
  · intro i hi
    have hn : i.rev ∉ J := fun hr =>
      hi (Finset.mem_image.mpr ⟨i.rev, hr, Fin.rev_rev i⟩)
    rw [diagramTwist_apply, diagramReversal_swap]
    exact h.inactive_fixed _ hn
  · intro i hi
    have hr : i.rev ∈ J := by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      simpa only [Fin.rev_rev] using hj
    rw [diagramTwist_apply, diagramTwist_apply, diagramReversal_swap, diagramReversal_lower]
    exact h.active_relation _ hr

theorem diagramTwist_injective {σ : Representation (ZMod 2) Group V}
    (hf : Function.Injective σ) : Function.Injective (diagramTwist σ) := by
  intro a b hab
  apply diagramReversal.injective
  apply hf
  simpa only [diagramTwist_apply] using hab

theorem diagramTwist_irreducible {σ : Representation (ZMod 2) Group V}
    (hi : IsIrreducible σ) : IsIrreducible (diagramTwist σ) :=
  (irreducible_comp_surjective_iff diagramReversal.toMonoidHom
    diagramReversal.surjective σ).mpr hi

/-- The twist has exactly the same action image, not just an isomorphic image. -/
theorem actionImage_diagramTwist (σ : Representation (ZMod 2) Group V) :
    actionImage (diagramTwist σ) = actionImage σ := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨diagramReversal g, Units.ext rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨diagramReversal.symm g, Units.ext ?_⟩
    change σ (diagramReversal (diagramReversal.symm g)) = σ g
    rw [MulEquiv.apply_symm_apply]

theorem linearNormalizer_diagramTwist (σ : Representation (ZMod 2) Group V) :
    linearNormalizer (diagramTwist σ) = linearNormalizer σ := by
  unfold linearNormalizer
  rw [actionImage_diagramTwist]

/-- Reversing the diagram retains every cubic elementary actor, including
actors outside the component image, with the same rank and fixed codimension. -/
theorem actor_gap_diagramTwist_iff (σ : Representation (ZMod 2) Group V) :
    (∀ A : Subgroup (linearNormalizer (diagramTwist σ)),
      IsElementaryTwo A → IsCubic (normalizerRepresentation (diagramTwist σ)) A →
      rank A ≤ 4 → 2 * rank A < fixedCodim (normalizerRepresentation (diagramTwist σ)) A) ↔
    (∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
      rank A ≤ 4 → 2 * rank A < fixedCodim (normalizerRepresentation σ) A) := by
  unfold normalizerRepresentation
  rw [linearNormalizer_diagramTwist]

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
