module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.OrbitImages

/-!
# Degree induction for nonprimitive alternating Sylow overgroups

Strong induction on the natural permutation degree combines the primitive
recognition input with the intransitive and transitive-imprimitive steps.
The small degrees and the whole-group case are discharged here through
`SmallDegrees`; `OrbitImages` supplies the actual component isomorphisms
once the orbit-image classifications have been established.

The two nonprimitive step hypotheses remain explicit. This is a conditional
assembly, not yet the requested theorem from primitive recognition alone.
Their producers must handle Sylow restriction, parity coupling and the
exceptional ambient degree before that theorem can be assembled.

Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85), final paragraph.
-/

public section
open Subgroup MulAction Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

theorem alternating_all_sylow_component_models_of_nonprimitive_steps
    (hprimitive : ∀ m : ℕ, 6 ≤ m → AlternatingPrimitiveComponentRecognition m)
    (hintransitive : ∀ m : ℕ, 6 ≤ m → AlternatingIntransitiveComponentStep m)
    (himprimitive : ∀ m : ℕ, 6 ≤ m → AlternatingImprimitiveComponentStep m)
    (m : ℕ) : AlternatingAllSylowComponentModels m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m ≤ 5
    · exact alternating_all_sylow_component_models_small hm
    have hm6 : 6 ≤ m := by omega
    intro S X hS D hD
    by_cases hX : X = ⊤
    · subst X
      exact alternating_top_component_models (by omega) D hD
    by_cases hp : IsPreprimitive X (Fin m)
    · exact alternating_primitive_component_models_of_recognition hm6
        (hprimitive m hm6) S X hS hX hp D hD
    by_cases ht : IsPretransitive X (Fin m)
    · exact himprimitive m hm6 ih S X hS hX ht hp D hD
    · exact hintransitive m hm6 ih S X hS hX ht D hD

theorem alternating_nonprimitive_component_recognition_of_steps
    (hprimitive : ∀ m : ℕ, 6 ≤ m → AlternatingPrimitiveComponentRecognition m)
    (hintransitive : ∀ m : ℕ, 6 ≤ m → AlternatingIntransitiveComponentStep m)
    (himprimitive : ∀ m : ℕ, 6 ≤ m → AlternatingImprimitiveComponentStep m)
    (m : ℕ) : AlternatingNonprimitiveComponentRecognition m := by
  intro S X hS hX hp D hD
  exact alternating_all_sylow_component_models_of_nonprimitive_steps
    hprimitive hintransitive himprimitive m S X hS D hD
end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
