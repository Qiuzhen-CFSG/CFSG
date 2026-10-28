module
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.SylowCoverage.Native
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.SylowCoverage.Certificate

/-!
# Large elementary subgroups of the native M24 Sylow subgroup

An arbitrary elementary subgroup supplies a clique in the certified graph of
square-one native elements. The checked branching certificate puts every clique
of cardinality at least 32 in one of six candidates. Four have order at most
32, so an elementary subgroup of order 64 equals one of the two established
six-generator candidates. No normality or catalogue assumption is used.

This is the finite Sylow input for Aschbacher–Smith H.14.1(1,5), printed
pp.396–397. Geometric identification and ambient fusion are supplied separately
by `Marking` and `FourFusions` and the owning chapter assembly.
-/

public section
namespace Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
open M24LocalGeometry
open scoped IsMulCommutative

/-- Each additional five-generator candidate has at most 32 elements. -/
theorem smallCandidate_card_le (i : Fin 4) : Nat.card (smallCandidate i) ≤ 32 :=
  SylowCoverage.smallCandidate_card_le i

/-- Exhaustive coverage for arbitrary large elementary subgroups of the native Sylow group. -/
theorem large_elementary_le_candidate (A : Subgroup M24) [IsElementaryAbelian 2 A]
    (hcard : 32 ≤ Nat.card A) (hA : A ≤ SylowNormalizer.candidate) :
    A ≤ EvenCandidates.elementary 0 ∨ A ≤ EvenCandidates.elementary 1 ∨
      ∃ i : Fin 4, A ≤ smallCandidate i := by
  classical
  let s : Finset (Fin 192) := Finset.univ.filter (fun v => (SylowCoverage.native v).val ∈ A)
  have hs (v : Fin 192) : v ∈ s ↔ (SylowCoverage.native v).val ∈ A := by simp [s]
  have cover (g : A) : ∃ v, (SylowCoverage.native v).val = g.val := by
    have hg : (⟨g.val, hA g.property⟩ : SylowNormalizer.candidate) ^ 2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian g.val g.property
    obtain ⟨v, hv⟩ := SylowCoverage.vertex_of_square _ hg
    exact ⟨v, congrArg Subtype.val hv⟩
  let f : s → A := fun v => ⟨(SylowCoverage.native v.val).val, (hs v.val).mp v.property⟩
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨v, hv⟩ := cover g
    exact ⟨⟨v, (hs v).mpr (hv.symm ▸ g.property)⟩, Subtype.ext hv⟩
  have hcs : 32 ≤ s.card := by
    have hc := hcard.trans (Nat.card_le_card_of_surjective f hf)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc
  obtain ⟨k, hk⟩ := SylowCoverage.clique_coverage s hcs (by
    intro v hv w hw
    have h : (SylowCoverage.native v).val * (SylowCoverage.native w).val =
        (SylowCoverage.native w).val * (SylowCoverage.native v).val :=
      congrArg (fun a : A => a.val) (mul_comm
        (⟨(SylowCoverage.native v).val, (hs v).mp hv⟩ : A)
        (⟨(SylowCoverage.native w).val, (hs w).mp hw⟩ : A))
    exact SylowCoverage.native_compatible v w (Subtype.ext h))
  have hle : A ≤ SylowCoverage.largeCandidate k := by
    intro g hg
    obtain ⟨v, hv⟩ := cover ⟨g, hg⟩
    have hmem := SylowCoverage.large_mask_mem k v (hk v ((hs v).mpr (hv.symm ▸ hg)))
    simpa only [hv] using hmem
  fin_cases k
  · exact Or.inr (Or.inr ⟨0, hle⟩)
  · exact Or.inr (Or.inr ⟨1, hle⟩)
  · exact Or.inr (Or.inr ⟨2, hle⟩)
  · exact Or.inr (Or.inr ⟨3, hle⟩)
  · exact Or.inl hle
  · exact Or.inr (Or.inl hle)

/-- The two existing E64 candidates are the only elementary order-64 subgroups of this Sylow group. -/
theorem elementary_card64_eq_candidate (A : Subgroup M24) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 64) (hA : A ≤ SylowNormalizer.candidate) :
    A = EvenCandidates.elementary 0 ∨ A = EvenCandidates.elementary 1 := by
  rcases large_elementary_le_candidate A (by omega) hA with h | h | ⟨i, h⟩
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, candidate_card]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, candidate_card]))
  · have hc := (Subgroup.card_le_of_le h).trans (smallCandidate_card_le i)
    omega

end Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
