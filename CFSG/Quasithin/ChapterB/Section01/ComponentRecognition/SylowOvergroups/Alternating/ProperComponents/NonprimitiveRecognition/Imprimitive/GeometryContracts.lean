module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.Imprimitive.BlockActions
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.Imprimitive.ImageInduction

/-!
# Geometric inputs for imprimitive alternating Sylow overgroups

These are two independent geometric assertions about the actual block maps.
The first controls elements that centralize the block kernel. The second
places an alternating Sylow subgroup in the relabelled even image on each
block and excludes seven-point blocks. Neither asserts a component model.

Source: the overgroup-structure argument at the end of Aschbacher–Smith
B.1.13, printed p.74 (PDF p.85). Their proofs are required before the
imprimitive induction step is unconditional.
-/

public section
open Subgroup MulAction Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- The even preimage uses the literal kernel restriction, relabelled only
by the canonical finite-set equivalence. -/
noncomputable abbrev alternatingBlockEvenImage {m : ℕ}
    (X : Subgroup (alternatingGroup (Fin m))) (B : Set (Fin m)) (C : orbit X B) :=
  alternatingEvenPreimage (alternatingBlockImage X B C) (Finite.equivFin C.val)

@[expose] def AlternatingBlockCentralizerControl (m : ℕ) : Prop :=
  ∀ (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))), (S : Subgroup _) ≤ X →
    IsPretransitive X (Fin m) →
    ∀ B : Set (Fin m), IsBlock X B → ¬ B.Subsingleton → B ≠ Set.univ →
      centralizer (alternatingBlockKernel X B : Set X) ≤ alternatingBlockKernel X B

@[expose] def AlternatingBlockSylowGeometry (m : ℕ) : Prop :=
  ∀ (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))), (S : Subgroup _) ≤ X →
    IsPretransitive X (Fin m) →
    ∀ B : Set (Fin m), IsBlock X B → ¬ B.Subsingleton → B ≠ Set.univ →
      Nat.card B ≠ 7 ∧ ∀ C : orbit X B,
        ∃ T : Sylow 2 (alternatingGroup (Fin (Nat.card C.val))),
          (T : Subgroup _) ≤ alternatingBlockEvenImage X B C

/-- The normal-subgroup component dichotomy is enough for placement;
components are not assumed normal in the ambient overgroup. -/
theorem alternating_component_le_blockKernel_of_centralizer {m : ℕ}
    (X : Subgroup (alternatingGroup (Fin m))) (B : Set (Fin m))
    (hcentral : centralizer (alternatingBlockKernel X B : Set X) ≤
      alternatingBlockKernel X B)
    (D : Subgroup X) (hD : IsComponent X D) : D ≤ alternatingBlockKernel X B := by
  rcases hD.normal_dichotomy (alternatingBlockKernel X B) with hle | hcomm
  · exact hle
  · exact (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hcentral

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
