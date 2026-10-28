module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Basic
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Coverage.Arithmetic

/-!
# All overlap automorphisms have the marked generator images

An automorphism preserves the ten checked element-order tests on the three
literal generators. The finite certificate covers every triple passing these
tests by conjugation and the two independent central changes. Transporting its
indices back to the actual 128-element overlap proves generator coverage with
no faithfulness, extension, or automorphism-classification premise.

This supplies exactly the coverage input of `all_extend_of_coverage` in the
parent assembly, for the genuine degree-24 Aut(M₁₂) pair and its nonsplit first
endpoint. Source context: Aschbacher--Smith F.1.12(I)(13), pp.262–263, and
14.2.21, p.988. Original ATLAS attribution is retained by the imported model.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions

/-- Every overlap automorphism has one of the predicted marked generator triples. -/
theorem generator_coverage : ∀ d : MulAut overlap, ∃ u : overlap, ∃ p q : Bool,
    ∀ j, d (Overlap.generator j) = generatorImage u p q j := by
  intro d
  obtain ⟨a, ha⟩ := Overlap.element_surjective (d (Overlap.generator 0))
  obtain ⟨b, hb⟩ := Overlap.element_surjective (d (Overlap.generator 1))
  obtain ⟨c, hc⟩ := Overlap.element_surjective (d (Overlap.generator 2))
  have ht : Coverage.admissible a b c := by
    apply (Coverage.admissible_iff a b c).mpr
    rw [ha, hb, hc]
    exact Coverage.groupAdmissible_map d _ _ _ Coverage.generators_admissible
  obtain ⟨u, p, q, hu⟩ := Coverage.coverage_indices a b c ht
  refine ⟨Overlap.element u, p, q, ?_⟩
  intro j
  have hj : Overlap.element (![a,b,c] j) = d (Overlap.generator j) := by
    fin_cases j
    · exact ha
    · exact hb
    · exact hc
  rw [← hj, hu j]
  exact Coverage.element_indexImage u p q j

end Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
