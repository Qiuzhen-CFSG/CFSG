module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.OrbitImages
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.Intransitive.PermutationModels
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.Intransitive.OrbitSylows

/-!
# The intransitive alternating component induction step

Every natural orbit is smaller than the original degree. Its literal action
image contains an alternating Sylow subgroup. In degree seven it contains
a symmetric Sylow subgroup, so transitivity and a transposition force the
full symmetric group and exclude the exceptional PSL₃(2) model. Degree
induction therefore classifies each orbit-image component with the original
ambient bound. The jointly faithful orbit projections eliminate the central
kernels and give an actual isomorphism for each original relative component.

The only recognition premise is the intentional smaller-degree induction
hypothesis in `AlternatingIntransitiveComponentStep`.

Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85), final paragraph.
-/

public section
open Subgroup MulAction Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- The intransitive branch of degree induction for components of alternating
Sylow overgroups, with no additional recognition or classification premise. -/
theorem alternating_intransitive_component_step (m : ℕ) (hm : 6 ≤ m) :
    AlternatingIntransitiveComponentStep m := by
  intro ih S X hS _ hnt D hD
  apply alternating_component_models_of_orbit_models X _ D hD
  intro a E hE
  classical
  obtain ⟨hA, h7⟩ := alternating_orbit_sylow_control hm S X hS hnt a
  have ht : IsPretransitive (alternatingOrbitImage X a) (orbit X a) := by
    let f : orbit X a →ₑ[alternatingOrbitProjection X a] orbit X a :=
      { toFun := id, map_smul' _ _ := rfl }
    exact IsPretransitive.of_surjective_map (f := f) Function.surjective_id inferInstance
  exact alternating_permutation_component_models_of_induction
    (by simpa only [Nat.card_eq_fintype_card] using alternating_orbit_degree_lt X hnt a)
    ih (alternatingOrbitImage X a) ht hA h7 E hE

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
