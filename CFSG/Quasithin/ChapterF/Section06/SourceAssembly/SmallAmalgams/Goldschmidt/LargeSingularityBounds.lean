module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LargeSingularity
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ShortSingularityKernels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ShortSingularityAlgebra
/-!
# The large branch begins at an odd singularity index at least five

The local residual exclusions first give an odd least singularity index.
A symmetric-three local quotient excludes length one. At length three,
the original singular arc selects the endpoint orientation in which the
radius-two kernel is the intersection of the local two-cores and has
index at most two in both. The proved finite local contradiction then
excludes that length as well.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(4.3)--(4.4), printed p.393. Both the witnesswise and existential forms
retain the actual arcs and action, for subsequent reorientation and the
general-case argument.
-/

public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}
/-- Every supplied least positive odd singularity index in the large
residual branch is at least five. -/
theorem CubicTreeAction.five_le_singularityIndex_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    {s : ℕ} (hs : 0 < s) (ho : Odd s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (q : BasedWalk (RankTwo.graph F) k v),
      k < s → q.Nonbacktracking → RightRegular (A := G) q)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p) : 5 ≤ s := by
  by_contra! hsmall
  have hs13 : s = 1 ∨ s = 3 := by obtain ⟨k, hk⟩ := ho; omega
  rcases hs13 with rfl | rfl
  · exact hn (h.one_arc_regular_of_symmetricThree p
      (h.stabilizer_quotient_symmetricThree_of_large_residual hC hA p.endpoint))
  · let i := v.type
    have hadj : (RankTwo.graph F).Adj (base F i) (base F (!i)) :=
      ⟨by change i ≠ !i; cases i <;> decide, incident_base F i (!i)⟩
    obtain ⟨he, hiA, hiB⟩ := h.short_singularity_core_kernels hshort p hp hn hadj rfl
    rw [show RankTwo.stabilizer F (base F i) = F i from stabilizer_base F i] at he hiA
    rw [show RankTwo.stabilizer F (base F (!i)) = F (!i) from stabilizer_base F (!i)] at he hiB
    have hCN := RankTwo.stabilizer_le_normalizer_ballKernel F (base F i) 2
    rw [show RankTwo.stabilizer F (base F i) = F i from stabilizer_base F i] at hCN
    exact h.false_of_short_core_intersection hC hA i (RankTwo.ballKernel F (base F i) 2)
      he hCN hiA hiB

/-- The original action supplies a least singular arc with odd length
at least five; no order, parity, or kernel premise remains. -/
theorem CubicTreeAction.exists_large_odd_singularityIndex_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4))) :
    ∃ s : ℕ, 5 ≤ s ∧ Odd s ∧
      (∀ (k : ℕ) (v : RankTwo.Vertex F) (q : BasedWalk (RankTwo.graph F) k v),
        k < s → q.Nonbacktracking → RightRegular (A := G) q) ∧
      ∃ (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) s v),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G) p := by
  obtain ⟨s, hs, ho, hshort, v, p, hp, hn⟩ := h.exists_odd_singularityIndex_of_large_residual hC hA
  exact ⟨s, h.five_le_singularityIndex_of_large_residual hC hA hs ho hshort p hp hn,
    ho, hshort, v, p, hp, hn⟩
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
