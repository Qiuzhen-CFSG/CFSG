module

public import Theory.GroupTheory.CharacteristicFrattiniAction
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.CoverFiveAction

/-!
# The covered image bounds from a marked inner five-action

Actors fixing X/O₂(X) centralize the inner X-action on O₂(X)/Φ(O₂(X)).
The characteristic Frattini-action theorem proves this for the literal
residualAction and sectionAction; it is no longer an extra model premise.

The source application therefore needs only the actual A₅ quotient,
the order256 Frattini section, and a fixed-point-free five-subgroup in its
inner X-action. The cover and natural-chief-factor construction remain
with the model producer. The full module endomorphism ring is not needed.

Source: Aschbacher–Smith, Lemma16.5.13, printed p.1202.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
variable {G : Type*} [Group G] [Finite G]

/-- The literal kernel image centralizes the inner residual action on its
Frattini section, without any model or module-centralizer hypothesis. -/
theorem section_kernelImage_le_innerCentralizer (V X : Subgroup G) :
    ((topAction (residualAction V X)).ker.map (sectionAction (residualAction V X))) ≤
      centralizer ((frattiniConjugation (pCore 2 X)).range : Set _) := by
  rintro a ⟨m, hm, rfl⟩
  have h := quotient_kernel_frattiniImage_le_centralizer
    (pCore 2 X) (p := 2) pCore_isPGroup
  apply h
  refine ⟨residualAction V X m, ?_, ?_⟩
  · exact hm
  · rfl

/-- Both intrinsic bounds follow from the marked natural inner five-action;
its centralization by the quotient kernel has been discharged. -/
theorem sourceImageBounds_of_inner_fixed_free_five (V X : Subgroup G)
    (e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))
    (hsection : Nat.card (pCore 2 X ⧸ frattini (pCore 2 X)) = 256)
    (A : Subgroup (MulAut (pCore 2 X ⧸ frattini (pCore 2 X))))
    (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A (pCore 2 X ⧸ frattini (pCore 2 X)) = ⊥)
    (hinner : A ≤ (frattiniConjugation (pCore 2 X)).range) :
    SourceImageBounds V X :=
  sourceImageBounds_of_alternating_five_and_fixed_free_five V X e hsection A hA hfixed
    ((section_kernelImage_le_innerCentralizer V X).trans (centralizer_le hinner))
end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
