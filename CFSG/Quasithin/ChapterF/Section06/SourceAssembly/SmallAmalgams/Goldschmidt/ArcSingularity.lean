module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcSetup
public import Theory.GroupAction.CubicTree.TotalSingularity

/-!
# Goldschmidt's singularity dichotomy

The rectangle argument changes a right failure to a left failure in the opposite
vertex orbit. Reversal changes the endpoint orbit according to the arc length.
An even first singular length therefore excludes regularity at either end for
all longer arcs. In the odd case, a longer regular arc has both endpoints in
the one surviving orbit, so its length is even.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.12),
printed pp.383--384.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem graphAction : GraphAction (RankTwo.graph F) G :=
  ⟨fun g _ _ h => (translationGraphIso F g).toHom.map_adj h⟩

theorem CubicTreeAction.left_nonregular_opposite (h : CubicTreeAction F) {s : ℕ}
    (hs : 0 < s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    {w : RankTwo.Vertex F} (q : BasedWalk (RankTwo.graph F) s w)
    (hq : q.Nonbacktracking) (ht : w.type ≠ v.type) : ¬ LeftRegular (A := G) q := by
  cases s with
  | zero => omega
  | succ s =>
    obtain ⟨z, hz, hr, hnr⟩ := shifted_not_leftRegular graphAction p hp
      (hshort s p.1 p.2 (by omega) (nonbacktracking_tail p hp)) hn
    have htype : w.type = (p.1 : RankTwo.Vertex F).type := by
      have ht' := p.1.property.1
      cases hw : w.type <;> cases hv : v.type <;>
        cases hp₁ : (p.1 : RankTwo.Vertex F).type <;> simp_all
    obtain ⟨g, hg⟩ := h.congruent_arcs (s + 1) hshort le_rfl q (p.2.snoc hz) hq hr htype
    exact fun hqreg => hnr (leftRegular_of_conjugate graphAction q _ g hg hqreg)

theorem CubicTreeAction.left_nonregular_even (h : CubicTreeAction F) {s : ℕ}
    (hs : 0 < s) (heven : Even s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    {w : RankTwo.Vertex F} (q : BasedWalk (RankTwo.graph F) s w)
    (hq : q.Nonbacktracking) : ¬ LeftRegular (A := G) q := by
  by_cases ht : w.type = v.type
  · have hend : v.type = p.endpoint.type := (RankTwo.even_walk_iff F p.toWalk).1
      (by simpa only [BasedWalk.length_toWalk] using heven)
    obtain ⟨g, hg⟩ := h.congruent_arcs s hshort le_rfl q (reverse p) hq
      (nonbacktracking_reverse p hp) (ht.trans hend)
    intro hqreg
    exact hn ((leftRegular_reverse_iff p).1
      (leftRegular_of_conjugate graphAction q _ g hg hqreg))
  · exact h.left_nonregular_opposite hs hshort p hp hn q hq ht

/-- If the first singular length is even, every longer arc fails regularity
at both endpoints. -/
theorem CubicTreeAction.nonregular_of_even (h : CubicTreeAction F) {s : ℕ}
    (hs : 0 < s) (heven : Even s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    {n : ℕ} (hsn : s ≤ n) {w : RankTwo.Vertex F}
    (q : BasedWalk (RankTwo.graph F) n w) (hq : q.Nonbacktracking) :
    ¬ LeftRegular (A := G) q ∧ ¬ RightRegular (A := G) q := by
  have hleft : ∀ {w : RankTwo.Vertex F} (r : BasedWalk (RankTwo.graph F) n w),
      r.Nonbacktracking → ¬ LeftRegular (A := G) r := by
    intro w r hr hreg
    exact h.left_nonregular_even hs heven hshort p hp hn (r.take s hsn)
      (BasedWalk.nonbacktracking_take hsn r hr) (leftRegular_take r hs hsn hreg)
  exact ⟨hleft q hq, fun hr => hleft (reverse q) (nonbacktracking_reverse q hq)
    ((leftRegular_reverse_iff q).2 hr)⟩

/-- A longer regular arc has both endpoints in the initial orbit of a right
singular arc. Its length is therefore even. -/
theorem CubicTreeAction.regular_endpoints (h : CubicTreeAction F) {s : ℕ}
    (hs : 0 < s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    {n : ℕ} (hsn : s ≤ n) {w : RankTwo.Vertex F}
    (q : BasedWalk (RankTwo.graph F) n w) (hq : q.Nonbacktracking)
    (hr : Regular (A := G) q) :
    w.type = v.type ∧ q.endpoint.type = v.type ∧ Even n := by
  have hleft : ∀ {w : RankTwo.Vertex F} (r : BasedWalk (RankTwo.graph F) n w),
      r.Nonbacktracking → LeftRegular (A := G) r → w.type = v.type := by
    intro w r hr hreg
    by_contra ht
    exact h.left_nonregular_opposite hs hshort p hp hn (r.take s hsn)
      (BasedWalk.nonbacktracking_take hsn r hr) ht (leftRegular_take r hs hsn hreg)
  have hstart := hleft q hq hr.1
  have hend := hleft (reverse q) (nonbacktracking_reverse q hq)
    ((leftRegular_reverse_iff q).2 hr.2)
  refine ⟨hstart, hend, ?_⟩
  simpa only [BasedWalk.length_toWalk] using
    (RankTwo.even_walk_iff F q.toWalk).2 (hstart.trans hend.symm)

/-- The source dichotomy, retaining both genuine endpoint regularity predicates. -/
theorem CubicTreeAction.singularity_dichotomy (h : CubicTreeAction F) {s : ℕ}
    (hs : 0 < s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p) :
    (∀ (n : ℕ) (w : RankTwo.Vertex F) (q : BasedWalk (RankTwo.graph F) n w),
      s ≤ n → q.Nonbacktracking → ¬ LeftRegular (A := G) q ∧ ¬ RightRegular (A := G) q) ∨
    (Odd s ∧ ∀ (n : ℕ) (w : RankTwo.Vertex F) (q : BasedWalk (RankTwo.graph F) n w),
      s ≤ n → q.Nonbacktracking → Regular (A := G) q →
        w.type = v.type ∧ q.endpoint.type = v.type ∧ Even n) := by
  by_cases he : Even s
  · exact Or.inl (fun n w q hsn hq => h.nonregular_of_even hs he hshort p hp hn hsn q hq)
  · exact Or.inr ⟨Nat.not_even_iff_odd.mp he,
      fun n w q hsn hq hr => h.regular_endpoints hs hshort p hp hn hsn q hq hr⟩

/-- In valence three the even branch is totally singular at both endpoints,
in the literal pointwise-fixer form used by the kernel propagation theorem. -/
theorem CubicTreeAction.totallySingular_of_even (h : CubicTreeAction F) {s : ℕ}
    (hs : 0 < s) (heven : Even s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    {n : ℕ} (hsn : s ≤ n) {w : RankTwo.Vertex F}
    (q : BasedWalk (RankTwo.graph F) n w) (hq : q.Nonbacktracking)
    (a : G) (ha : ∀ y ∈ q.vertices, a • y = y) :
    (∀ z, Theory.GroupAction.CubicTree.Forward q z → a • z = z) ∧
    (∀ z, Backward q z → a • z = z) := by
  have hnot := h.nonregular_of_even hs heven hshort p hp hn hsn q hq
  cases n with
  | zero => omega
  | succ n =>
    exact ⟨fun _ hz => fixes_forward_of_not_rightRegular graphAction q
      (h.card_neighbor q.endpoint) hnot.2 a ha hz,
      fun _ hz => fixes_backward_of_not_leftRegular graphAction q
      (h.card_neighbor w) hnot.1 a ha hz⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
