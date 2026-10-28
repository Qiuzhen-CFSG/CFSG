module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.SourceCases

/-!
# The literal simple-QTKE embedding for Hall escape

The image of the nontrivial two-core is normalized by the embedded group.
Its proper two-local normalizer is SQTK by the actual ambient hypothesis.
Restriction gives SQTK on the original carrier, so the proved source cases
apply without changing its generation parameter or its Sylow subgroup.

Source: Aschbacher–Smith 4.4.13(1), pp.623–624.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels ChapterB
universe u
variable {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]

/-- The actual embedded parabolic inherits SQTK from its nontrivial
ambient two-local normalizer. -/
theorem sqtk_of_embedding_with_nontrivial_twoCore
    {Kc : GroupClass.{u}} (hG : IsSimpleQTKE Kc G) (f : X →* G)
    (hf : Function.Injective f) (hcore : pCore 2 X ≠ ⊥) : IsSQTK Kc X := by
  let Q := (pCore 2 X).map f
  have hQ : Q ≠ ⊥ := fun hh => hcore ((map_eq_bot_iff_of_injective _ hf).mp hh)
  have hn : f.range ≤ normalizer (Q : Set G) := by
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map] using
      (pCore 2 X).le_normalizer_map f
  have hs := hG.twoLocal_sqtk
    (show IsTwoLocal (normalizer (Q : Set G)) from ⟨Q,hQ,pCore_isPGroup.map f,rfl⟩)
  let j : X →* normalizer (Q : Set G) := f.codRestrict _ (fun x => hn ⟨x,rfl⟩)
  have hj : Function.Injective j := fun x y hh => hf (congrArg Subtype.val hh)
  exact ⟨hs.stronglyQuasithin.of_injective j hj,hs.isKGroup.of_injective j hj⟩

/-- The original hypotheses of 4.4.13 supply the actual binary source
rows, retaining the original carrier and both quotient maps. -/
theorem source_embedded_binary_cases_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (f : X →* G)
    (hf : Function.Injective f) (hcore : pCore 2 X ≠ ⊥)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hn : 1 < generationParameter X) :
    ∃ (K : Subgroup X) (n : ℕ), K.IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ 1 < n ∧
      ReducedCases (minimalParabolicMax S hP) K S n :=
  source_binary_cases_knownSimple (sqtk_of_embedding_with_nontrivial_twoCore hG f hf hcore) S hP hn

/-- The source selection also retains generation by this very component
and the original Sylow subgroup, as needed by the exchanged row. -/
theorem source_embedded_generating_binary_cases_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (f : X →* G)
    (hf : Function.Injective f) (hcore : pCore 2 X ≠ ⊥)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hn : 1 < generationParameter X) :
    ∃ (K : Subgroup X) (n : ℕ), K.IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (S : Subgroup X) = ⊤ ∧ 1 < n ∧
      ReducedCases (minimalParabolicMax S hP) K S n :=
  source_binary_cases_generating_knownSimple
    (sqtk_of_embedding_with_nontrivial_twoCore hG f hf hcore) S hP hn

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
