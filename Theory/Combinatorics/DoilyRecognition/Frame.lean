module

public import Theory.Combinatorics.DoilyRecognition.Local
public import Theory.Combinatorics.DoilyRecognition.Matching

/-!
# Triangle frames for the (15,6,1,3) graph

The three outside-neighbor matchings furnish coordinates for every vertex.
This retains the original vertices and all incidence maps in the doily recognition.
-/

@[expose] public section

namespace Theory.Combinatorics.Doily
abbrev FrameVertex := Fin 3 ⊕ (Fin 3 × (Bool × Bool))
variable {Ω:Type*} [Fintype Ω] [DecidableEq Ω]
variable (G:SimpleGraph Ω) [DecidableRel G.Adj]
structure Frame where
  vertex : FrameVertex ≃ Ω
  base_adj : ∀i j,G.Adj (vertex (.inl i)) (vertex (.inl j)) ↔ i≠j
  mixed_adj : ∀i j p,G.Adj (vertex (.inl i)) (vertex (.inr (j,p))) ↔ i=j
  fiber_adj : ∀i p q,G.Adj (vertex (.inr (i,p))) (vertex (.inr (i,q))) ↔ p.1=q.1 ∧ p.2≠q.2

variable {G}
theorem exists_frame (h:G.IsSRGWith 15 6 1 3) : Nonempty (Frame G) := by
  classical
  obtain ⟨t⟩:=exists_triangle h
  have hm (i:Fin 3):∃e:(Bool×Bool)≃{x//x∈t.block i},
      ∀p q,G.Adj (e p) (e q) ↔ p.1=q.1 ∧ p.2≠q.2 := by
    apply matching_four_coordinates (G.induce {x|x∈t.block i})
    · change Fintype.card ↥(t.block i) = 4
      simpa only [Fintype.card_coe] using t.block_card h i
    · intro x
      obtain ⟨y,hy,hu⟩:=t.block_matching h i x x.property
      exact ⟨⟨y,hy.1⟩,hy.2,fun z hz=>Subtype.ext (hu z ⟨z.property,hz⟩)⟩
  choose e he using hm
  let f:FrameVertex→Ω:=fun x=>match x with
    | .inl i=>t.point i
    | .inr (i,p)=>(e i p).val
  have hf:Function.Injective f:=by
    intro x y hxy
    rcases x with i|⟨i,p⟩ <;> rcases y with j|⟨j,q⟩
    · exact congrArg Sum.inl (t.injective hxy)
    · exact ((t.mem_block.mp (e j q).property).2 i hxy.symm).elim
    · exact ((t.mem_block.mp (e i p).property).2 j hxy).elim
    · change (e i p).val = (e j q).val at hxy
      have hij:i=j:=by
        by_contra hh
        exact Finset.disjoint_left.mp (t.block_disjoint h hh) (e i p).property
          (hxy.symm ▸ (e j q).property)
      subst j
      have hp:p=q:=(e i).injective (Subtype.ext hxy)
      exact hp ▸ rfl
  have hs:Function.Surjective f:=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,by simp [FrameVertex,h.card]⟩ |>.2
  let E:FrameVertex≃Ω:=Equiv.ofBijective f ⟨hf,hs⟩
  refine ⟨⟨E,?_,?_,?_⟩⟩
  · intro i j
    change G.Adj (t.point i) (t.point j) ↔ i≠j
    exact ⟨fun ha hij=>ha.ne (congrArg t.point hij),t.adjacent i j⟩
  · intro i j p
    change G.Adj (t.point i) (e j p).val ↔ i=j
    constructor
    · intro ha
      by_contra hh
      have hbi:(e j p).val∈t.block i:=t.mem_block.mpr ⟨ha,(t.mem_block.mp (e j p).property).2⟩
      exact Finset.disjoint_left.mp (t.block_disjoint h hh) hbi (e j p).property
    · intro hij
      subst j
      exact (t.mem_block.mp (e i p).property).1
  · intro i p q
    exact he i p q
end Theory.Combinatorics.Doily
