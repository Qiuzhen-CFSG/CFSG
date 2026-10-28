module
public import CFSG.Quasithin.Chapter5.A5Source.Complete
public import CFSG.Quasithin.Chapter4.Section03.A5.SourceCrossing

/-!
# A genuine source counterexample forced by Baumann escape

An escaping Baumann normalizer forces the original L to be an alternating
five block. The completed crossing argument says that uniqueness over L
would already control that normalizer. Its failure therefore supplies the
original outside maximal two-local H with T ∩ H Sylow in H, controlled
normalizer, and uniqueness above every strict extension inside T.

All inputs are the original A₅ context and the alleged Baumann escape.
The remaining source 4.3.2 component and model contradictions must exclude
this configuration before claiming unconditional 5.1.7(1).
Source: Aschbacher–Smith 5.1.7(1), pp.633–634, using 4.3.2–3, pp.613–614.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- Baumann escape supplies the actual maximal-intersection source choice. -/
theorem exists_source_sylow_counterexample_of_baumann_escape
    (d : Context T L V V₁ V₂ V₃)
    (hout : ¬ normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ∃ H : Subgroup G, IsMaximalTwoLocal H ∧ L ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ⊓ H < (T : Subgroup G) ∧
      normalizer ((T : Subgroup G) ⊓ H : Set G) ≤ normalizer (L : Set G) ∧
      (∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ H) ∧
      ∀ X : Subgroup G, (T : Subgroup G) ⊓ H < X → X ≤ (T : Subgroup G) →
        Chapter4.UniqueMaximalOvergroup (L ⊔ X) (normalizer (L : Set G)) := by
  have hb := (alternating_block_of_baumann_escape d hout).2.1
  exact d.exists_source_sylow_counterexample hb
    (fun hu => hout (baumann_normalizer_of_source_uniqueness d hu))

/-- The same alleged Baumann escape supplies the original crossing actor. -/
theorem exists_source_crossing_counterexample_of_baumann_escape
    (d : Context T L V V₁ V₂ V₃)
    (hout : ¬ normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ∃ (H : Subgroup G) (t : G), IsMaximalTwoLocal H ∧ L ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧
      (∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ H) ∧
      t ∈ (T : Subgroup G) ∧ t ∉ (T : Subgroup G) ⊓ H ∧
      t ∈ normalizer ((T : Subgroup G) ⊓ H : Set G) ∧
      t ^ 2 ∈ (T : Subgroup G) ⊓ H ∧
      Chapter4.UniqueMaximalOvergroup (L ⊔ ((T : Subgroup G) ⊓ H ⊔ zpowers t))
        (normalizer (L : Set G)) ∧
      (∀ W : Subgroup G, IsPGroup 2 W → W ≠ ⊥ →
        L ⊔ ((T : Subgroup G) ⊓ H ⊔ zpowers t) ≤ normalizer (W : Set G) →
        normalizer (W : Set G) ≤ normalizer (L : Set G)) := by
  have hb := (alternating_block_of_baumann_escape d hout).2.1
  exact d.exists_source_crossing_counterexample hb
    (fun hu => hout (baumann_normalizer_of_source_uniqueness d hu))

end CFSG.Quasithin.Chapter5.A5Source
