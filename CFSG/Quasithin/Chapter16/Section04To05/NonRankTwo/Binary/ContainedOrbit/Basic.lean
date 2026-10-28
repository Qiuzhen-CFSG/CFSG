module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.Setup
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.Action
public import Theory.SpecificGroups.OrthogonalFourBinary.IndexTwoNormalizer.Geometry

/-!
# Marked local action for the contained branch

A conjugate of z in KL cannot have a two-central L-projection: its conjugate
of K is detected in Δ₀, where the earlier two-central exclusion applies.
This deduction uses the actual conjugate and the actual commuting factors.

`LocalAction` specifies coordinates for A and its point stabilizer, including
compatibility with conjugation and the two-central class. It is a construction
contract, not an assertion that the coordinates exist. In particular it contains
no orbit lengths, generation assertion, or stabilizer order.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1200–1201, the contained-A branch of Lemma 16.5.12. The allowable orbit
class is j₂; the second printed j₁ in the orbit paragraph is a typographical error.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary.ContainedOrbit

open Subgroup MulAction
open OrthogonalFourBinary

variable {G : Type*} [Group G]

/-- A two-central component projection, retaining both actual commuting factors. -/
def HasTwoCentralProjection (L : Subgroup G) (x : G) : Prop :=
  ∃ c ∈ centralizer (L : Set G), ∃ v ∈ L, x = c * v ∧ IsTwoCentralIn L v

/-- The earlier Δ₀ detector rules out a two-central projection of any conjugate of z. -/
theorem conjugate_not_twoCentralProjection [Finite G]
    {T : Sylow 2 G} {z u g : G} {L R X : Subgroup G}
    (h : EarlierInputs T z L g R X u)
    (hdis : Disjoint L (centralizer (L : Set G))) (y : G) :
    ¬ HasTwoCentralProjection L (MulAut.conj y z) := by
  rintro ⟨c, hc, v, hv, he, htwo⟩
  have hzK : z ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.mp (h.component.1 hl)
  have hiJ : MulAut.conj y z ∈ (centralizer (L : Set G)).conjBy y :=
    ⟨z, hzK, rfl⟩
  have hi2 : orderOf (MulAut.conj y z) = 2 :=
    ((MulAut.conj y).orderOf_eq z).trans h.involution
  have hiKL : MulAut.conj y z ∈ centralizer (L : Set G) ⊔ L := by
    rw [he]
    exact mul_mem_sup hc hv
  have hiK : MulAut.conj y z ∉ centralizer (L : Set G) := by
    intro hi
    have hvK : v ∈ centralizer (L : Set G) := by
      have hh := (centralizer (L : Set G)).mul_mem
        ((centralizer (L : Set G)).inv_mem hc) hi
      simpa only [he, inv_mul_cancel_left] using hh
    have hv1 := Subgroup.disjoint_def.mp hdis hv hvK
    have hv2 := htwo.1
    simp [hv1] at hv2
  have hJ := h.detect _ ⟨y, rfl⟩ _ hiJ hi2 hiKL hiK
  exact h.avoid_twoCentral hdis _ hJ _ c v hiJ hi2 hc hv he htwo

/-- Coordinates for E₁₆ × ⟨z⟩. The first factor carries the split quadratic form. -/
abbrev CoordinateGroup := Multiplicative Space × Multiplicative F

/-- The distinguished central factor generator in the coordinates. -/
def centralVector : CoordinateGroup := (1, Multiplicative.ofAdd 1)

/-- The full quadratic isometry group O₄⁺(2), acting on the given four-space. -/
abbrev OrthogonalGroup := IndexTwoNormalizer.IsometryGroup

/-- Coordinates and the full stabilizer action, with their actual conjugation
compatibility. Constructing this witness remains a local-model obligation. -/
structure LocalAction (L A : Subgroup G) (z : A) where
  coordinates : A ≃* CoordinateGroup
  central_coordinate : coordinates z = centralVector
  actor : stabilizer (normalizerImage A) z ≃* OrthogonalGroup
  intertwines : ∀ (m : stabilizer (normalizerImage A) z) (a : A),
    coordinates (m • a) =
      (Multiplicative.ofAdd ((actor m).val (Multiplicative.toAdd (coordinates a).1)),
        (coordinates a).2)
  singular_projection : ∀ a : A, (coordinates a).1 ≠ 1 →
    (form (Multiplicative.toAdd (coordinates a).1) = 0 ↔
      HasTwoCentralProjection L (a : G))

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary.ContainedOrbit
