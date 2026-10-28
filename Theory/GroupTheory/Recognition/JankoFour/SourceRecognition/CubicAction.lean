module

public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CoreAction
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicNormalizer

/-!
# The source cubic subgroup acts faithfully on Q/Z(Q)

The Sylow complement maps isomorphically onto the retained cubic kernel in
H/Q. Composing that inclusion with the faithful H/Q action proves faithfulness
for the very same cubic subgroup. The action equation is the original left
conjugation action, and the final existence theorem constructs X and the
normalizer product without any additional local-geometry hypotheses.

This supplies part of the setup of (4.1). In particular, a faithful cubic
action is not yet the fixed-point-free action needed for its GF(4) conclusion.
Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.1), printed p.597.
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

open Subgroup LocalGeometry

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The cubic complement acts on the literal central quotient of Q. -/
noncomputable def cubicAction (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
    (X : Sylow 3 (CubicLift.subgroup e)) :
    X →* MulAut (core z ⧸ center (core z)) :=
  (coreQuotientAction h).comp
    (e.projection.ker.subtype.comp (cubicKernelEquiv e h X).toMonoidHom)

theorem cubicAction_injective (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
    (X : Sylow 3 (CubicLift.subgroup e)) :
    Function.Injective (cubicAction h e X) :=
  (coreQuotientAction_injective h).comp
    (e.projection.ker.subtype_injective.comp (cubicKernelEquiv e h X).injective)

@[simp] theorem cubicAction_mk (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
    (X : Sylow 3 (CubicLift.subgroup e)) (x : X) (q : core z) :
    cubicAction h e X x (QuotientGroup.mk' (center (core z)) q) =
      QuotientGroup.mk' (center (core z))
        (MulAut.conjNormal ((x : CubicLift.subgroup e) : centralizer z) q) :=
  coreQuotientAction_mk h _ q

/-- Construct the source cubic subgroup, its faithful action, and the actual
normalizer product from IsTypeJ4, without a supplied local subgroup package. -/
theorem exists_cubic_normalizer_action (h : IsTypeJ4 z) :
    ∃ (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
      (X : Sylow 3 (CubicLift.subgroup e)),
      Nat.card X = 3 ∧ Function.Injective (cubicAction h e X) ∧
        ∀ g : centralizer z,
          ∃ q : core z, ∃ n : normalizer (cubicSylowImage e X : Set (centralizer z)),
            (q : centralizer z) * n = g := by
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (CubicLift.subgroup e)))
  exact ⟨e, X, cubicSylow_card e h X, cubicAction_injective h e X,
    exists_core_mul_cubicNormalizer e h X⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

end
