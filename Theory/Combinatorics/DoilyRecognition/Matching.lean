module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

/-!
# Matching coordinates for the doily

A four-vertex graph with exactly one neighbor at each vertex admits literal two-edge coordinates. The proof chooses the two edges and retains their original endpoints; no graph enumeration is used.
-/

@[expose] public section

namespace Theory.Combinatorics.Doily
variable {Ω:Type*} [Fintype Ω] [DecidableEq Ω]
variable (G:SimpleGraph Ω) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem matching_four_coordinates (hc:Fintype.card Ω=4)
    (hm:∀x,∃!y,G.Adj x y) :
    ∃e:(Bool×Bool)≃Ω,∀p q,G.Adj (e p) (e q) ↔ p.1=q.1 ∧ p.2≠q.2 := by
  have hn:Nonempty Ω:=Fintype.card_pos_iff.mp (by rw [hc];decide)
  obtain ⟨x⟩:=hn
  obtain ⟨y,hxy,hy⟩:=hm x
  have hxyne:=hxy.ne
  have hex:∃z:Ω,z≠x∧z≠y:=by
    by_contra! hh
    have hu:(Finset.univ:Finset Ω)⊆{x,y}:=by
      intro z _
      simp only [Finset.mem_insert,Finset.mem_singleton]
      by_cases hz:z=x
      · exact Or.inl hz
      · exact Or.inr (hh z hz)
    have hb:=Finset.card_le_card hu
    rw [Finset.card_univ,hc,Finset.card_pair hxyne] at hb
    omega
  obtain ⟨z,hzx,hzy⟩:=hex
  obtain ⟨w,hzw,hw⟩:=hm z
  have hzwne:=hzw.ne
  have hwx:w≠x:=by
    intro he
    have he':G.Adj x z:=he ▸ hzw.symm
    exact hzy (hy z he')
  have hwy:w≠y:=by
    intro he
    obtain ⟨a,ha,hau⟩:=hm y
    have h1:=hau x hxy.symm
    have h2:=hau z (he ▸ hzw.symm)
    exact hzx (h2.trans h1.symm)
  let f:Bool×Bool→Ω:=fun p=>if p.1 then (if p.2 then w else z) else (if p.2 then y else x)
  have hf:Function.Injective f:=by
    rintro ⟨a,b⟩ ⟨c,d⟩ he
    cases a <;> cases b <;> cases c <;> cases d <;> dsimp [f] at he ⊢
    all_goals first
      | rfl
      | exact (hxyne he).elim
      | exact (hxyne he.symm).elim
      | exact (hzx he).elim
      | exact (hzx he.symm).elim
      | exact (hzy he).elim
      | exact (hzy he.symm).elim
      | exact (hzwne he).elim
      | exact (hzwne he.symm).elim
      | exact (hwx he).elim
      | exact (hwx he.symm).elim
      | exact (hwy he).elim
      | exact (hwy he.symm).elim
  have hs:Function.Surjective f:=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,by simp [hc]⟩ |>.2
  let e:(Bool×Bool)≃Ω:=Equiv.ofBijective f ⟨hf,hs⟩
  have hnxz:¬G.Adj x z:=fun hh=>hzy (hy z hh)
  have hnxw:¬G.Adj x w:=fun hh=>hwy (hy w hh)
  have hnyz:¬G.Adj y z:=by
    intro hh
    obtain ⟨a,ha,hau⟩:=hm y
    exact hzx ((hau z hh).trans (hau x hxy.symm).symm)
  have hnyw:¬G.Adj y w:=by
    intro hh
    obtain ⟨a,ha,hau⟩:=hm y
    exact hwx ((hau w hh).trans (hau x hxy.symm).symm)
  refine ⟨e,?_⟩
  rintro ⟨a,b⟩ ⟨c,d⟩
  change G.Adj (f (a,b)) (f (c,d)) ↔ a=c ∧ b≠d
  cases a <;> cases b <;> cases c <;> cases d <;> dsimp [f]
  · exact iff_of_false G.irrefl (by decide)
  · exact iff_of_true hxy (by decide)
  · exact iff_of_false hnxz (by decide)
  · exact iff_of_false hnxw (by decide)
  · exact iff_of_true hxy.symm (by decide)
  · exact iff_of_false G.irrefl (by decide)
  · exact iff_of_false hnyz (by decide)
  · exact iff_of_false hnyw (by decide)
  · exact iff_of_false (fun hh=>hnxz hh.symm) (by decide)
  · exact iff_of_false (fun hh=>hnyz hh.symm) (by decide)
  · exact iff_of_false G.irrefl (by decide)
  · exact iff_of_true hzw (by decide)
  · exact iff_of_false (fun hh=>hnxw hh.symm) (by decide)
  · exact iff_of_false (fun hh=>hnyw hh.symm) (by decide)
  · exact iff_of_true hzw.symm (by decide)
  · exact iff_of_false G.irrefl (by decide)

end Theory.Combinatorics.Doily
