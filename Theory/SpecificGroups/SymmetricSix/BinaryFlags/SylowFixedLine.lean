module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
/-!
# The line containing the Sylow-fixed natural six-letter vectors

For A₆ ≤ H ≤ S₆, conjugate the canonical even Sylow into the prescribed
Sylow of H. The known uniqueness of its invariant line shows that every
nonzero fixed vector spans the same transported duad line. In particular
all fixed vectors lie in the span of any one nonzero fixed vector.

Source: Aschbacher–Smith B.3.4 and 3.3.31, printed pp.84–85 and 602.
-/

public section
open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

/-- One marking identifies the spans of all nonzero fixed vectors. -/
theorem fixed_vectors_span_eq (H : Subgroup S) (hH : alternatingGroup Ω ≤ H)
    (T : Sylow 2 H) : ∃ g : H,
      ∀ v : V, v ≠ 0 →
      (∀ x ∈ (T : Subgroup H).map H.subtype, naturalRepresentation Ω x v = v) →
      Submodule.span (ZMod 2) {v} = move g canonicalLine := by
  obtain ⟨g, hg⟩ := exists_conjugate_T0_le H hH T
  refine ⟨g, fun v hv hf => ?_⟩
  apply (invariant_unique_conjugate T0 le_rfl g _ ?_).1 (finrank_span_singleton hv)
  intro x hx
  simp only [move, Submodule.map_span, Set.image_singleton, hf x (hg hx)]

/-- All Sylow-fixed vectors lie on the line spanned by any nonzero one. -/
theorem fixed_vectors_le_span (H : Subgroup S) (hH : alternatingGroup Ω ≤ H)
    (T : Sylow 2 H) (v : V) (hv : v ≠ 0)
    (hf : ∀ x ∈ (T : Subgroup H).map H.subtype, naturalRepresentation Ω x v = v)
    (w : V) (hw : ∀ x ∈ (T : Subgroup H).map H.subtype, naturalRepresentation Ω x w = w) :
    w ∈ Submodule.span (ZMod 2) {v} := by
  obtain ⟨g, hg⟩ := fixed_vectors_span_eq H hH T
  by_cases h0 : w = 0
  · rw [h0]; exact Submodule.zero_mem _
  · rw [hg v hv hf, ← hg w h0 hw]
    exact Submodule.subset_span (by simp)
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
