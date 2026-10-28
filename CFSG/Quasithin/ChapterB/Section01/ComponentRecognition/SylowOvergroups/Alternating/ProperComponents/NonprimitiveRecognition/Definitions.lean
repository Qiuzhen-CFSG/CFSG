module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.Reduction

/-!
# Induction contracts for nonprimitive alternating Sylow overgroups

The induction property includes the whole alternating group and the small
degrees, since action images need not be proper and can have small degree.
The two step contracts retain the literal natural action and relative
component condition. They assume classification only at strictly smaller
degrees; they do not assert either step.

Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85), final paragraph.
The intransitive step must account for symmetric orbit images and parity.
The imprimitive step must account for the kernel of the action on blocks.
Both steps must preserve the exceptional restriction on the ambient degree.
-/

public section
open Subgroup MulAction Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

@[expose] def AlternatingAllSylowComponentModels (m : ℕ) : Prop :=
  ∀ (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))), (S : Subgroup _) ≤ X →
    ∀ D : Subgroup X, IsComponent X D → AlternatingSubgroupModels m D

@[expose] def AlternatingIntransitiveComponentStep (m : ℕ) : Prop :=
  (∀ n : ℕ, n < m → AlternatingAllSylowComponentModels n) →
  ∀ (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))), (S : Subgroup _) ≤ X → X ≠ ⊤ →
    ¬ IsPretransitive X (Fin m) →
    ∀ D : Subgroup X, IsComponent X D → AlternatingSubgroupModels m D

@[expose] def AlternatingImprimitiveComponentStep (m : ℕ) : Prop :=
  (∀ n : ℕ, n < m → AlternatingAllSylowComponentModels n) →
  ∀ (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))), (S : Subgroup _) ≤ X → X ≠ ⊤ →
    IsPretransitive X (Fin m) → ¬ IsPreprimitive X (Fin m) →
    ∀ D : Subgroup X, IsComponent X D → AlternatingSubgroupModels m D

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
