module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Sections
public import Theory.GroupTheory.NormalJoinQuotientProduct

/-!
# The three marked summands of the lower G.2.5 section

The first two pair intersections lie in W, so their join intersects the
third pair intersection in exactly the triple intersection S₂. The
quotient kernel then proves disjointness and spanning of the literal
three images in S₃/S₂. This is the internal direct sum in G.2.5(6),
before recognition of its dual natural action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(6), printed pp.335–336.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Setup
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  (d : LinearThree.Hypothesis D F n g h)
include d

/-- Directness of the three actual pair-intersection images. Together
with `lower_elementary`, these clauses are their internal binary direct sum.
No nontriviality of any marked summand is required. -/
theorem lower_marked_direct (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    [((S₂ D g h).subgroupOf (S₃ D g h)).Normal] :
    let A := lowerImage D g h (W D g h ⊓ conjugate (W D g h) g)
    let B := lowerImage D g h (W D g h ⊓ conjugate (W D g h) h)
    let C := lowerImage D g h (conjugate (W D g h) g ⊓ conjugate (W D g h) h)
    Disjoint A B ∧ IsCompl (A ⊔ B) C := by
  let A := W D g h ⊓ conjugate (W D g h) g
  let B := W D g h ⊓ conjugate (W D g h) h
  let C := conjugate (W D g h) g ⊓ conjugate (W D g h) h
  let P := S₃ D g h
  let E := S₂ D g h
  let q := QuotientGroup.mk' (E.subgroupOf P)
  have hAB : A ⊓ B = E := by
    dsimp only [E]
    rw [d.S₂_eq_triple_W hUT hf hLI]
    dsimp [A, B]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hx.1.1, hx.2⟩⟩
  have hABC : (A ⊔ B) ⊓ C = E := by
    dsimp only [E]
    rw [d.S₂_eq_triple_W hUT hf hLI]
    apply le_antisymm
    · have hw : A ⊔ B ≤ W D g h := sup_le inf_le_left inf_le_left
      intro x hx
      exact ⟨⟨hw hx.1, hx.2.1⟩, hx.2.2⟩
    · intro x hx
      exact ⟨mem_sup_left hx.1, hx.1.2, hx.2⟩
  have hAP : A ≤ P := le_sup_left.trans le_sup_left
  have hBP : B ≤ P := le_sup_right.trans le_sup_left
  have hqAB : q.ker = A.subgroupOf P ⊓ B.subgroupOf P := by
    rw [QuotientGroup.ker_mk', ← hAB]
    rfl
  have hqABC : q.ker = (A ⊔ B).subgroupOf P ⊓ C.subgroupOf P := by
    rw [QuotientGroup.ker_mk', ← hABC]
    rfl
  change Disjoint ((A.subgroupOf P).map q) ((B.subgroupOf P).map q) ∧
    IsCompl (((A.subgroupOf P).map q) ⊔ ((B.subgroupOf P).map q)) ((C.subgroupOf P).map q)
  refine ⟨disjoint_map_of_ker_eq_inf q _ _ hqAB, ?_⟩
  rw [← Subgroup.map_sup, ← subgroupOf_sup hAP hBP]
  refine ⟨disjoint_map_of_ker_eq_inf q _ _ hqABC, ?_⟩
  apply Subgroup.codisjoint_map (QuotientGroup.mk'_surjective _)
  exact codisjoint_subgroupOf_sup (A ⊔ B) C

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
